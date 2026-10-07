#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""vx — 最小文件置乱工具。

设计要点：
  - 无外部口令文件：全部置乱参数由「口令 + 每文件随机盐」经 PBKDF2 拉伸后
    由 HMAC-SHA256 计数器流确定性生成，任何参数不落盘、不产出任何伴随文件。
  - 容器仅 21 字节头：salt(16) + 掩码填充长度(1) + 掩码校验标签(4)，
    无魔数、无版本、无字段名，头部统计上与随机噪声不可区分。
  - 填充对齐 16 字节、最短 128 字节、随机追加 0~2 块；参数域约束：
    组数下限 8、步长与组内长度互素、退化组合拒绝。
用法：
  python vx.py lock <file> [-p PASS]
  python vx.py unlock <file> [-p PASS]
不传 -p 时交互式输入口令。错误口令会在校验标签处被拒绝。
"""

import argparse
import getpass
import hashlib
import hmac
import os
import sys
from math import gcd

BLOCK = 16
MIN_LEN = 128
EXTRA_MAX = 2
G_FLOOR = 8
G_CAP = 1024
ROUNDS_LO, ROUNDS_HI = 8, 24
KDF_ITER = 200_000
SALT_LEN = 16
TAG_LEN = 4
HEAD_LEN = SALT_LEN + 1 + TAG_LEN
SUFFIX = ".vx"


class Stream:
    """HMAC-SHA256 计数器确定性字节流。"""

    def __init__(self, seed: bytes):
        self.k = hmac.new(seed, b"stream", hashlib.sha256).digest()
        self.ctr = 0
        self.buf = b""

    def read(self, n: int) -> bytes:
        while len(self.buf) < n:
            self.ctr += 1
            self.buf += hmac.new(self.k, str(self.ctr).encode(), hashlib.sha256).digest()
        out, self.buf = self.buf[:n], self.buf[n:]
        return out

    def below(self, m: int) -> int:
        """均匀随机 [0, m)。拒绝采样消除模偏置。"""
        if m <= 0:
            raise ValueError("bound must be positive")
        nb = max(1, (m - 1).bit_length() // 8 + 1)
        limit = (256 ** nb) // m * m
        while True:
            v = int.from_bytes(self.read(nb), "big")
            if v < limit:
                return v % m


def derive_seed(passphrase: str, salt: bytes) -> bytes:
    return hashlib.pbkdf2_hmac(
        "sha256", passphrase.encode("utf-8"), salt, KDF_ITER, dklen=32
    )


def _divisor_choices(n2: int):
    return [d for d in range(G_FLOOR, min(n2 // 2, G_CAP) + 1) if n2 % d == 0]


def gen_params(n2: int, st: Stream):
    """参数域约束下的确定性参数生成（含退化拒绝，锁定/解锁两侧共享同一消耗序列）。"""
    while True:
        ds = _divisor_choices(n2)
        g = ds[st.below(len(ds))]
        L = n2 // g
        order = list(range(g))
        for i in range(g - 1, 0, -1):
            j = st.below(i + 1)
            order[i], order[j] = order[j], order[i]
        phase = [st.below(L) for _ in range(g)]
        stride = []
        for _ in range(g):
            while True:
                c = st.below(L) + 1
                if gcd(c, L) == 1:
                    stride.append(c)
                    break
        passes = ROUNDS_LO + st.below(ROUNDS_HI - ROUNDS_LO + 1)
        if not _degenerate(g, order, phase, stride):
            return g, L, order, phase, stride, passes


def composite_map(n2: int, g: int, L: int, order, phase, stride, passes):
    base = [0] * n2
    for r in range(g):
        s = order[r]
        v = phase[r] % L
        qr = stride[r] % L
        for j in range(L):
            base[r * L + j] = s + g * v
            v += qr
            if v >= L:
                v -= L
    m = list(range(n2))
    for _ in range(passes):
        m = [base[x] for x in m]
    return m


def _degenerate(g, order, phase, stride):
    return order == list(range(g)) and not any(phase) and all(x == 1 for x in stride)


def lock_bytes(data: bytes, passphrase: str) -> bytes:
    salt = os.urandom(SALT_LEN)
    seed = derive_seed(passphrase, salt)
    st = Stream(seed)

    # 流消耗顺序（锁定/解锁两侧必须严格一致）：
    #   padx(1B) -> extra 块数 -> 填充内容(pad B) -> 参数 -> 校验标签(4B)
    padx = st.read(1)[0]
    extra = st.below(EXTRA_MAX + 1)
    blocks = -(-max(len(data), 1) // BLOCK)
    target = max(MIN_LEN, blocks * BLOCK) + BLOCK * extra
    pad = target - len(data)
    stored_pad = pad ^ padx
    padded = data + st.read(pad)

    g, L, order, phase, stride, passes = gen_params(target, st)
    m = composite_map(target, g, L, order, phase, stride, passes)
    out = [0] * target
    for w in range(target):
        out[m[w]] = padded[w]
    body = bytes(out)

    tagx = bytes(a ^ b for a, b in zip(hashlib.sha256(data).digest()[:TAG_LEN], st.read(TAG_LEN)))
    return salt + bytes([stored_pad]) + tagx + body


def unlock_bytes(blob: bytes, passphrase: str) -> bytes:
    if len(blob) < HEAD_LEN + BLOCK:
        raise ValueError("container too short")
    salt = blob[:SALT_LEN]
    stored_pad = blob[SALT_LEN]
    tagx = blob[SALT_LEN + 1: SALT_LEN + 1 + TAG_LEN]
    cipher = blob[HEAD_LEN:]
    n2 = len(cipher)

    seed = derive_seed(passphrase, salt)
    st = Stream(seed)
    padx = st.read(1)[0]
    pad = stored_pad ^ padx
    if pad > n2:
        raise ValueError("container corrupt")
    st.below(EXTRA_MAX + 1)   # 对齐：消耗 extra 块数抽取（与锁定侧一致）
    st.read(pad)              # 跳过填充内容，恢复流对齐

    g, L, order, phase, stride, passes = gen_params(n2, st)
    m = composite_map(n2, g, L, order, phase, stride, passes)
    # 还原 = 正向散射的逆: P[w] = C[m[w]]（与 lock 的 out[m[w]] = P[w] 互逆）
    full = [0] * n2
    for w in range(n2):
        full[w] = cipher[m[w]]
    plain_padded = bytes(full)

    expect = bytes(a ^ b for a, b in
                   zip(hashlib.sha256(plain_padded[: n2 - pad]).digest()[:TAG_LEN], st.read(TAG_LEN)))
    if expect != tagx:
        raise ValueError("passphrase mismatch")
    return plain_padded[: n2 - pad]


def _passphrase(args) -> str:
    if args.passphrase is not None:
        return args.passphrase
    p1 = getpass.getpass("passphrase: ")
    if getattr(args, "confirm", False):
        p2 = getpass.getpass("confirm   : ")
        if p1 != p2:
            print("error: passphrase mismatch", file=sys.stderr)
            sys.exit(2)
    return p1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="vx", description="file scrambler")
    sub = ap.add_subparsers(dest="mode", required=True)
    for name in ("lock", "unlock"):
        sp = sub.add_parser(name)
        sp.add_argument("file")
        sp.add_argument("-p", "--passphrase", default=None)
    if argv is None:
        argv = sys.argv[1:]
    if not argv:
        ap.print_help()
        return 2
    mode = argv[0]
    if mode not in ("lock", "unlock"):
        print(f"error: unknown mode {mode!r}", file=sys.stderr)
        return 2
    args = ap.parse_args([mode] + argv[1:])

    try:
        with open(args.file, "rb") as f:
            blob = f.read()
    except OSError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    pass_ = _passphrase(args)

    if mode == "lock":
        out_path = args.file + SUFFIX
        if os.path.exists(out_path):
            print(f"error: {out_path} already exists (remove it first)", file=sys.stderr)
            return 1
        out = lock_bytes(blob, pass_)
    else:
        out_path = args.file[: -len(SUFFIX)] if args.file.endswith(SUFFIX) else args.file + ".out"
        if os.path.exists(out_path):
            print(f"error: {out_path} already exists (remove it first)", file=sys.stderr)
            return 1
        try:
            out = unlock_bytes(blob, pass_)
        except ValueError as e:
            print(f"error: {e}", file=sys.stderr)
            return 1

    with open(out_path, "wb") as f:
        f.write(out)
    print(f"{mode}ed: {out_path} ({len(out)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
