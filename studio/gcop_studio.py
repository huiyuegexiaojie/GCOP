#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
gcop_studio.py — GCOP 工作台（三模式文件混淆 · 结果不落盘）

三个模式（核心都是 GCOP 循环轨道置换引擎）:
  钥匙模式  随机参数 + 钥匙文件 .gcop.key（与 gcop.py v2 完全兼容）
  口令模式  PBKDF2(口令) 派生参数，自包含容器 .vx（与 vx.py 完全兼容）
  混合模式  随机钥匙种子 + 口令派生 XOR 合成参数流 —— 钥匙与口令缺一不可（.hx + .hx.key）

算法公开声明（Kerckhoffs 原则，2026-10）:
  本程序的全部算法 —— GCOP 多轮置换结构、PBKDF2 口令派生、HMAC 计数器流、
  混合模式的种子 XOR 构造、三种容器格式 —— 均按「公开可审查」标准编写并公开。
  安全性不依赖算法保密，只依赖秘密本身：
    钥匙模式  = 钥匙文件的保管（文件被拷走即失守）
    口令模式  = 口令熵（算法公开后攻击者获得离线验证预言机，弱口令会被字典/GPU 爆破）
    混合模式  = 钥匙与口令同时保密（缺一即不可解）
  该性质已经两轮 AI 红蓝对抗实测验证：攻击方完整复原算法后，
  强口令容器仍不可破（详见 GCOP黑箱逆向难度评估报告）。

GUI 特性:
  - 结果不落盘：混淆/解密产物仅存于本程序内存（右侧列表），关闭即销毁
  - 手动导出：把列表项拖到资源管理器（拖出瞬间才写临时文件），或右键「导出为…」
  - 三种容器都支持拖入解密（按扩展名自动识别 .gcop / .vx / .hx）
  - 双击列表项可预览内容；右键有更多操作
"""

import json
import math
import os
import queue
import random
import shutil
import sys
import tempfile
import threading
import hashlib
import hmac
from math import gcd

# ============================================================================
# 引擎 A：GCOP v2 核心（与 gcop.py v2 逐字节兼容）
# ============================================================================


class ParamError(Exception):
    pass


def gcop_map_fwd(n, g, sigma, a, q):
    """GCOP 正向读索引表: Y[r*L+j] = X[sigma[r] + g*((a[r]+q[r]*j) mod L)]"""
    L = n // g
    m = [0] * n
    for r in range(g):
        s = sigma[r]
        v = a[r] % L
        qr = q[r] % L
        for j in range(L):
            m[r * L + j] = s + g * v
            v += qr
            if v >= L:
                v -= L
    return m


def _composite_map(n, g, sigma, a, q, rounds):
    base = gcop_map_fwd(n, g, sigma, a, q)
    m = list(range(n))
    for _ in range(rounds):
        m = [base[x] for x in m]
    return m


def gcop_obfuscate(data, g, sigma, a, q, rounds):
    m = _composite_map(len(data), g, sigma, a, q, rounds)
    return bytes(map(data.__getitem__, m))


def gcop_restore(cipher, K):
    """按钥匙字典还原；兼容 v1（无 pad）与 v2 钥匙。"""
    n = K["n"]
    g = K["g"]
    if len(cipher) != n:
        raise ParamError(f"密文长度 {len(cipher)} 与钥匙记录 n={n} 不符")
    if g < 1 or n % g:
        raise ParamError(f"钥匙损坏：n={n} 不能被 g={g} 整除")
    gs = n // g
    sigma, a, q, rounds = K["sigma"], K["a"], K["q"], K["rounds"]
    G = list(range(n))
    for _ in range(rounds):
        groups = [[G[j + m * g] for m in range(gs)] for j in range(g)]
        groups = [groups[sigma[j]] for j in range(g)]
        newG = [0] * n
        for j, gb in enumerate(groups):
            for m, v in enumerate(gb):
                newG[j * gs + m] = v
        groups = [newG[j * gs:(j + 1) * gs] for j in range(g)]
        groups = [[gb[(a[j] + q[j] * m) % gs] for m in range(gs)]
                  for j, gb in enumerate(groups)]
        G = [x for gb in groups for x in gb]
    full = [0] * n
    for m in range(n):
        full[G[m]] = cipher[m]
    pad = K.get("pad", 0)
    return bytes(full[:n - pad]) if pad else bytes(full)


_PAD_BLOCK = 16
_PAD_MIN = 128
_PAD_RAND_EXTRA = 2
_G_FLOOR = 8
_AUTO_G_CAP = 1024
_ROUNDS_LO, _ROUNDS_HI = 8, 24
_IDENTITY_CHECK_LIMIT = 1 << 16


def pad_for_obfuscation(data, rng=None):
    """填充：16 对齐 + 最短 128B + 随机追加 0~2 块。返回 (填充后, pad)。"""
    rng = rng or random.SystemRandom()
    n = len(data)
    blocks = -(-max(n, 1) // _PAD_BLOCK)
    target = max(_PAD_MIN, blocks * _PAD_BLOCK) + _PAD_BLOCK * rng.randint(0, _PAD_RAND_EXTRA)
    pad = target - n
    if pad <= 0:
        return data, 0
    return data + os.urandom(pad), pad


def _proper_divisors(n):
    divs = {1}
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            base = set(divs)
            pk = 1
            while m % p == 0:
                m //= p
                pk *= p
                divs |= {d * pk for d in base}
        p += 1 if p == 2 else 2
    if m > 1:
        divs |= {d * m for d in divs}
    return sorted(d for d in divs if 0 < d < n)


def _random_coprime(rng, L):
    while True:
        c = rng.randint(1, L - 1)
        if gcd(c, L) == 1:
            return c


def _is_degenerate(g, sigma, a, q):
    return (sigma == list(range(g)) and not any(a) and all(x == 1 for x in q))


def auto_generate_params(n, rng=None):
    rng = rng or random.SystemRandom()
    hi = min(n // 2, _AUTO_G_CAP)
    divs = [d for d in _proper_divisors(n) if _G_FLOOR <= d <= hi]
    if not divs:
        divs = [d for d in _proper_divisors(n) if 2 <= d <= hi]
    if not divs:
        divs = [1]
    g = rng.choice(divs)
    L = n // g
    sigma = list(range(g))
    rng.shuffle(sigma)
    a = [rng.randrange(L) for _ in range(g)]
    q = [_random_coprime(rng, L) for _ in range(g)]
    rounds = rng.randint(_ROUNDS_LO, _ROUNDS_HI)
    if _is_degenerate(g, sigma, a, q):
        return auto_generate_params(n, rng)
    if n <= _IDENTITY_CHECK_LIMIT:
        m = _composite_map(n, g, sigma, a, q, rounds)
        if m == list(range(n)):
            return auto_generate_params(n, rng)
    return g, sigma, a, q, rounds


# ============================================================================
# 引擎 B：口令派生核心（与 vx.py 逐字节兼容；extra_seed 供混合模式使用）
# ============================================================================

KDF_ITER = 200_000
SALT_LEN = 16
TAG_LEN = 4
HEAD_LEN = SALT_LEN + 1 + TAG_LEN
BLOCK = 16
MIN_LEN = 128
EXTRA_MAX = 2


class Stream:
    """HMAC-SHA256 计数器确定性字节流。"""

    def __init__(self, seed):
        self.k = hmac.new(seed, b"stream", hashlib.sha256).digest()
        self.ctr = 0
        self.buf = b""

    def read(self, n):
        while len(self.buf) < n:
            self.ctr += 1
            self.buf += hmac.new(self.k, str(self.ctr).encode(), hashlib.sha256).digest()
        out, self.buf = self.buf[:n], self.buf[n:]
        return out

    def below(self, m):
        if m <= 0:
            raise ValueError("bound must be positive")
        nb = max(1, (m - 1).bit_length() // 8 + 1)
        limit = (256 ** nb) // m * m
        while True:
            v = int.from_bytes(self.read(nb), "big")
            if v < limit:
                return v % m


def derive_seed(passphrase, salt, extra_seed=None):
    """口令 → 32B 种子。extra_seed（混合模式的钥匙种子）与之 XOR 后使用。"""
    base = hashlib.pbkdf2_hmac(
        "sha256", passphrase.encode("utf-8"), salt, KDF_ITER, dklen=32
    )
    if extra_seed is None:
        return base
    if len(extra_seed) != 32:
        raise ValueError("钥匙种子长度必须为 32 字节")
    return bytes(a ^ b for a, b in zip(base, extra_seed))


def gen_params(n2, st):
    """参数域约束下的确定性参数生成（含退化拒绝；锁定/解锁共享同一消耗序列）。"""
    while True:
        hi = min(n2 // 2, _AUTO_G_CAP)
        ds = [d for d in range(_G_FLOOR, hi + 1) if n2 % d == 0]
        if not ds:
            ds = [d for d in range(2, hi + 1) if n2 % d == 0]
        if not ds:
            ds = [1]
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
        passes = _ROUNDS_LO + st.below(_ROUNDS_HI - _ROUNDS_LO + 1)
        if not (order == list(range(g)) and not any(phase) and all(x == 1 for x in stride)):
            return g, L, order, phase, stride, passes


def composite_map(n2, g, L, order, phase, stride, passes):
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


def lock_bytes(data, passphrase, extra_seed=None):
    salt = os.urandom(SALT_LEN)
    seed = derive_seed(passphrase, salt, extra_seed)
    st = Stream(seed)
    # 流消耗顺序（锁定/解锁两侧严格一致）:
    #   padx(1B) -> extra 块数 -> 填充内容 -> 参数 -> 校验标签(4B)
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
    tagx = bytes(a ^ b for a, b in
                 zip(hashlib.sha256(data).digest()[:TAG_LEN], st.read(TAG_LEN)))
    return salt + bytes([stored_pad]) + tagx + body


def unlock_bytes(blob, passphrase, extra_seed=None):
    if len(blob) < HEAD_LEN + BLOCK:
        raise ValueError("容器太短，不是有效的混淆容器")
    salt = blob[:SALT_LEN]
    stored_pad = blob[SALT_LEN]
    tagx = blob[SALT_LEN + 1: SALT_LEN + 1 + TAG_LEN]
    cipher = blob[HEAD_LEN:]
    n2 = len(cipher)
    seed = derive_seed(passphrase, salt, extra_seed)
    st = Stream(seed)
    padx = st.read(1)[0]
    pad = stored_pad ^ padx
    if pad > n2:
        raise ValueError("校验失败：口令错误或容器已损坏")
    st.below(EXTRA_MAX + 1)
    st.read(pad)
    g, L, order, phase, stride, passes = gen_params(n2, st)
    m = composite_map(n2, g, L, order, phase, stride, passes)
    full = [0] * n2
    for w in range(n2):
        full[w] = cipher[m[w]]
    plain_padded = bytes(full)
    expect = bytes(a ^ b for a, b in
                   zip(hashlib.sha256(plain_padded[: n2 - pad]).digest()[:TAG_LEN],
                       st.read(TAG_LEN)))
    if expect != tagx:
        raise ValueError("口令错误")
    return plain_padded[: n2 - pad]


# ============================================================================
# 引擎 C：三模式统一入口
# ============================================================================

MODES = ("key", "pass", "hybrid")
MODE_NAME = {"key": "钥匙模式", "pass": "口令模式", "hybrid": "混合模式"}
KIND_NAME = {"container": "容器", "key": "钥匙", "plain": "明文"}

GCOP_KEY_TYPE = "gcop-key"
HYBRID_KEY_TYPE = "hybrid-key"


def _uq_name(name: str, used: set) -> str:
    """在 used 集合内取不重名。"""
    if name not in used:
        used.add(name)
        return name
    stem, dot, ext = name.rpartition(".")
    if not dot:
        stem, ext = name, ""
    i = 2
    while True:
        cand = f"{stem} ({i})" + (f".{ext}" if ext else "")
        if cand not in used:
            used.add(cand)
            return cand
        i += 1


def obfuscate_bytes(data: bytes, mode: str, passphrase=None, rng=None):
    """统一混淆入口。返回 [(kind, bytes, suffix)]，suffix 相对原文件名。

    key    -> [("container", 密文, ".gcop"), ("key", 钥匙JSON, ".gcop.key")]
    pass   -> [("container", 容器, ".vx")]
    hybrid -> [("container", 容器, ".hx"), ("key", 钥匙JSON, ".hx.key")]
    """
    if mode not in MODES:
        raise ValueError(f"未知模式 {mode!r}")
    if mode in ("pass", "hybrid") and not passphrase:
        raise ValueError("口令模式 / 混合模式需要口令")
    out = []
    if mode == "key":
        padded, pad = pad_for_obfuscation(data, rng)
        g, sigma, a, q, rounds = auto_generate_params(len(padded), rng)
        container = gcop_obfuscate(padded, g, sigma, a, q, rounds)
        key_obj = {"type": GCOP_KEY_TYPE, "version": 2, "n": len(container), "g": g,
                   "pad": pad, "sigma": list(sigma), "a": list(a), "q": list(q),
                   "rounds": rounds}
        out.append(("container", container, ".gcop"))
        out.append(("key", json.dumps(key_obj, ensure_ascii=False).encode("utf-8"), ".gcop.key"))
    elif mode == "pass":
        out.append(("container", lock_bytes(data, passphrase), ".vx"))
    else:  # hybrid
        key_seed = os.urandom(32)
        container = lock_bytes(data, passphrase, extra_seed=key_seed)
        key_obj = {"type": HYBRID_KEY_TYPE, "version": 1, "seed": key_seed.hex()}
        out.append(("container", container, ".hx"))
        out.append(("key", json.dumps(key_obj).encode("utf-8"), ".hx.key"))
    return out


def load_key_obj(key_bytes: bytes) -> dict:
    """钥匙字节 -> 字典（含类型校验）。"""
    try:
        obj = json.loads(key_bytes.decode("utf-8"))
    except Exception as e:
        raise ValueError(f"钥匙文件不是有效的 JSON：{e}")
    if not isinstance(obj, dict) or "type" not in obj:
        raise ValueError("钥匙文件缺少 type 字段")
    return obj


def restore_bytes(container: bytes, mode: str, passphrase=None, key_obj=None) -> bytes:
    """统一还原入口。key/hybrid 模式必须提供 key_obj 字典。"""
    if mode == "key":
        if key_obj is None:
            raise ValueError("钥匙模式还原需要钥匙")
        return gcop_restore(container, key_obj)
    if mode == "pass":
        return unlock_bytes(container, passphrase)
    if mode == "hybrid":
        if key_obj is None:
            raise ValueError("混合模式还原需要钥匙")
        if key_obj.get("type") != HYBRID_KEY_TYPE:
            raise ValueError("这不是混合模式的钥匙文件")
        try:
            seed = bytes.fromhex(key_obj["seed"])
        except Exception:
            raise ValueError("混合钥匙的种子字段损坏")
        return unlock_bytes(container, passphrase, extra_seed=seed)
    raise ValueError(f"未知模式 {mode!r}")


def sniff_container(path: str):
    """按扩展名识别容器模式；返回 'key'/'pass'/'hybrid' 或 None。"""
    low = path.lower()
    if low.endswith(".vx"):
        return "pass"
    if low.endswith(".hx"):
        return "hybrid"
    if low.endswith(".gcop"):
        return "key"
    return None


def entropy_bits(pw: str) -> float:
    pool = 0
    if any(c.islower() for c in pw):
        pool += 26
    if any(c.isupper() for c in pw):
        pool += 26
    if any(c.isdigit() for c in pw):
        pool += 10
    if any(not c.isalnum() for c in pw):
        pool += 33
    return len(pw) * math.log2(pool) if pw and pool else 0.0


def human_size(n: int) -> str:
    if n < 1024:
        return f"{n} B"
    if n < 1024 * 1024:
        return f"{n/1024:.1f} KB"
    return f"{n/1024/1024:.2f} MB"


# ============================================================================
# 临时导出管理：只有用户主动拖出/导出时才写临时文件
# ============================================================================


class TempExports:
    def __init__(self):
        self.dir = None
        self._seq = 0

    def _ensure_dir(self):
        if self.dir is None:
            self.dir = os.path.join(tempfile.gettempdir(), "gcop_studio_export")
            os.makedirs(self.dir, exist_ok=True)
        return self.dir

    def write(self, name: str, data: bytes) -> str:
        d = self._ensure_dir()
        base = name
        path = os.path.join(d, base)
        while os.path.exists(path):
            self._seq += 1
            stem, dot, ext = base.rpartition(".")
            if not dot:
                stem, ext = base, ""
            path = os.path.join(d, f"{stem} ({self._seq})" + (f".{ext}" if ext else ""))
        with open(path, "wb") as f:
            f.write(data)
        return path

    def cleanup(self):
        if self.dir and os.path.isdir(self.dir):
            shutil.rmtree(self.dir, ignore_errors=True)
        self.dir = None


# ============================================================================
# GUI
# ============================================================================


def run_gui():
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox

    BG, CARD, ACCENT = "#eef2f8", "#ffffff", "#3b82f6"
    OK, ERR, DIM, DARK = "#16a34a", "#dc2626", "#64748b", "#1e293b"
    FONT = "Microsoft YaHei UI"

    try:
        from tkinterdnd2 import TkinterDnD, DND_FILES
        root = TkinterDnD.Tk()
        dnd = True
    except Exception:
        root = tk.Tk()
        DND_FILES = "DND_Files"
        dnd = False

    class VirtualItem:
        __slots__ = ("name", "data", "kind", "mode", "pair", "iid")

        def __init__(self, name, data, kind, mode, pair=None):
            self.name, self.data, self.kind, self.mode = name, data, kind, mode
            self.pair = pair
            self.iid = None

    class DecryptDialog(tk.Toplevel):
        """模态解密对话框：按需收集口令 / 钥匙文件路径。"""

        def __init__(self, parent, title, need_pw, key_state, key_hint):
            super().__init__(parent)
            self.result = None
            self.transient(parent)
            self.title(title)
            self.configure(bg=BG)
            self.resizable(False, False)
            frm = tk.Frame(self, bg=CARD, padx=18, pady=16)
            frm.pack(fill="both", expand=True, padx=12, pady=12)
            tk.Label(frm, text=title, font=(FONT, 11, "bold"), bg=CARD, fg=DARK
                     ).pack(anchor="w", pady=(0, 8))

            self.pw_var = tk.StringVar()
            if need_pw:
                row = tk.Frame(frm, bg=CARD)
                row.pack(fill="x", pady=3)
                tk.Label(row, text="口令：", font=(FONT, 10), bg=CARD, fg=DARK
                         ).pack(side="left")
                ent = tk.Entry(row, textvariable=self.pw_var, show="•",
                               font=(FONT, 10), width=30, relief="flat",
                               highlightthickness=1, highlightbackground="#cbd5e1",
                               highlightcolor=ACCENT)
                ent.pack(side="left", fill="x", expand=True)
                ent.focus_set()

            self.key_var = tk.StringVar(value=key_hint)
            self.key_entry = None
            if key_state == "browse":
                row = tk.Frame(frm, bg=CARD)
                row.pack(fill="x", pady=(8, 3))
                tk.Label(row, text="钥匙：", font=(FONT, 10), bg=CARD, fg=DARK
                         ).pack(side="left")
                self.key_entry = tk.Entry(row, textvariable=self.key_var,
                                          font=(FONT, 9), width=28, relief="flat",
                                          highlightthickness=1,
                                          highlightbackground="#cbd5e1",
                                          highlightcolor=ACCENT)
                self.key_entry.pack(side="left", fill="x", expand=True)
                tk.Button(row, text="浏览…", font=(FONT, 9), relief="flat",
                          bg="#e2e8f0", activebackground="#cbd5e1",
                          command=self._browse).pack(side="left", padx=(6, 0))
            elif key_state == "auto":
                tk.Label(frm, text="钥匙：✓ 已自动配对", font=(FONT, 9),
                         bg=CARD, fg=OK).pack(anchor="w", pady=(4, 0))

            btns = tk.Frame(frm, bg=CARD)
            btns.pack(fill="x", pady=(14, 0))
            tk.Button(btns, text="取消", font=(FONT, 10), relief="flat", bg="#e2e8f0",
                      width=8, command=self.destroy).pack(side="right", padx=(8, 0))
            tk.Button(btns, text="解 密", font=(FONT, 10, "bold"), relief="flat",
                      bg=ACCENT, fg="white", activebackground="#2563eb",
                      width=10, command=self._ok).pack(side="right")
            self.bind("<Return>", lambda e: self._ok())
            self.bind("<Escape>", lambda e: self.destroy())
            self.grab_set()
            self.wait_window(self)

        def _browse(self):
            p = filedialog.askopenfilename(
                title="选择钥匙文件", parent=self,
                filetypes=[("钥匙文件", "*.key"), ("所有文件", "*.*")])
            if p:
                self.key_var.set(p)

        def _ok(self):
            self.result = {"pw": self.pw_var.get(),
                           "key_path": self.key_var.get().strip() or None}
            self.destroy()

    class StudioApp:
        def __init__(self):
            self.items = {}            # iid -> VirtualItem
            self._seq = 0
            self._used_names = set()
            self._q = queue.Queue()
            self.busy = False
            self.temp = TempExports()

            root.title("GCOP 工作台 — 三模式文件混淆 · 结果不落盘")
            root.geometry("980x640")
            root.minsize(880, 560)
            root.configure(bg=BG)
            root.protocol("WM_DELETE_WINDOW", self._close)

            # ---------- 顶栏 ----------
            top = tk.Frame(root, bg=CARD)
            top.pack(fill="x")
            inner = tk.Frame(top, bg=CARD)
            inner.pack(fill="x", padx=16, pady=10)
            tk.Label(inner, text="GCOP 工作台", font=(FONT, 15, "bold"),
                     bg=CARD, fg=DARK).pack(side="left")
            tk.Label(inner, text="钥匙 · 口令 · 混合 三模式｜结果仅存于内存，关闭即销毁｜算法公开 · 安全仅依赖钥匙与口令",
                     font=(FONT, 9), bg=CARD, fg=DIM).pack(side="left", padx=12)

            # ---------- 主区 ----------
            main = tk.Frame(root, bg=BG)
            main.pack(fill="both", expand=True, padx=12, pady=10)

            # ===== 左侧：模式 + 口令 + 拖放 =====
            left = tk.Frame(main, bg=BG, width=330)
            left.pack(side="left", fill="y", padx=(0, 10))
            left.pack_propagate(False)

            modecard = tk.Frame(left, bg=CARD)
            modecard.pack(fill="x", ipady=8, pady=(0, 8))
            tk.Label(modecard, text="混淆模式", font=(FONT, 10, "bold"),
                     bg=CARD, fg=DARK).pack(anchor="w", padx=12, pady=(6, 2))
            self.mode_var = tk.StringVar(value="key")
            self._mode_btns = {}
            for val, label in (
                    ("key", "钥匙模式 — 随机钥匙文件（.gcop）"),
                    ("pass", "口令模式 — 口令派生（.vx）"),
                    ("hybrid", "混合模式 — 钥匙 + 口令 双保险（.hx）")):
                rb = tk.Radiobutton(modecard, text=label, variable=self.mode_var,
                                    value=val, font=(FONT, 10), bg=CARD, fg=DARK,
                                    selectcolor=CARD, activebackground=CARD,
                                    anchor="w", command=self._mode_changed)
                rb.pack(fill="x", padx=12)
                self._mode_btns[val] = rb

            # 口令区（口令/混合模式显示）
            self.pwcard = tk.Frame(left, bg=CARD)
            self.pwcard.pack(fill="x", pady=(0, 8), ipady=8)
            tk.Label(self.pwcard, text="口令", font=(FONT, 10, "bold"),
                     bg=CARD, fg=DARK).pack(anchor="w", padx=12, pady=(6, 2))
            prow = tk.Frame(self.pwcard, bg=CARD)
            prow.pack(fill="x", padx=12)
            self.pw_var = tk.StringVar()
            self.pw_ent = tk.Entry(prow, textvariable=self.pw_var, show="•",
                                   font=(FONT, 11), relief="flat",
                                   highlightthickness=1,
                                   highlightbackground="#cbd5e1",
                                   highlightcolor=ACCENT)
            self.pw_ent.pack(fill="x", ipady=3)
            self.pw_ent.bind("<KeyRelease>", lambda e: self._pw_hint_update())
            self.pw_hint = tk.Label(self.pwcard, text="", font=(FONT, 9),
                                    bg=CARD, fg=DIM, anchor="w")
            self.pw_hint.pack(fill="x", padx=12, pady=(3, 2))

            # 拖放卡
            self.drop = tk.Label(
                left, justify="center", cursor="hand2",
                font=(FONT, 11), fg=DARK,
                text=("将文件拖到这里\n\n"
                      "普通文件 → 按左侧模式混淆\n"
                      ".gcop / .vx / .hx → 自动识别并解密\n\n"
                      "结果只出现在右侧列表，不写入磁盘")
                if dnd else
                ("拖拽引擎未安装（pip install tkinterdnd2）\n点击此处选择文件\n\n"
                 "结果只出现在右侧列表，不写入磁盘"))
            self.drop.pack(fill="both", expand=True, ipady=30)
            self._set_drop_bg(False)
            self.drop.bind("<Button-1>", lambda e: self._choose_files())
            if dnd:
                self.drop.bind("<Enter>", lambda e: self._set_drop_bg(True))
                self.drop.bind("<Leave>", lambda e: self._set_drop_bg(False))
                try:
                    root.drop_target_register(DND_FILES)
                    root.dnd_bind("<<Drop>>", self._on_drop)
                except Exception:
                    pass

            self.status = tk.Label(left, text="就绪", font=(FONT, 9), bg=BG,
                                   fg=DIM, anchor="w", wraplength=310,
                                   justify="left")
            self.status.pack(fill="x", pady=(8, 0))

            # ===== 右侧：结果列表 =====
            right = tk.Frame(main, bg=CARD)
            right.pack(side="left", fill="both", expand=True)

            rhead = tk.Frame(right, bg=CARD)
            rhead.pack(fill="x", padx=12, pady=(10, 4))
            tk.Label(rhead, text="结果列表（仅存于内存）", font=(FONT, 10, "bold"),
                     bg=CARD, fg=DARK).pack(side="left")
            tk.Label(rhead, text="双击预览 · 右键更多 · 拖到资源管理器即导出",
                     font=(FONT, 9), bg=CARD, fg=DIM).pack(side="right")

            cols = ("name", "kind", "mode", "size")
            style = ttk.Style()
            try:
                style.configure("Studio.Treeview", rowheight=26,
                                font=(FONT, 10), background="white",
                                fieldbackground="white")
                style.configure("Studio.Treeview.Heading", font=(FONT, 10, "bold"))
            except Exception:
                pass
            tf = tk.Frame(right, bg=CARD)
            tf.pack(fill="both", expand=True, padx=12, pady=(0, 4))
            self.tree = ttk.Treeview(tf, columns=cols, show="headings",
                                     style="Studio.Treeview", selectmode="extended")
            for cid, text, w, anchor in (
                    ("name", "名称", 300, "w"), ("kind", "类型", 70, "center"),
                    ("mode", "模式", 90, "center"), ("size", "大小", 90, "e")):
                self.tree.heading(cid, text=text)
                self.tree.column(cid, width=w, anchor=anchor)
            vs = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
            self.tree.configure(yscrollcommand=vs.set)
            self.tree.pack(side="left", fill="both", expand=True)
            vs.pack(side="right", fill="y")

            self.tree.bind("<Double-1>", lambda e: self._preview())
            self.tree.bind("<<TreeSelect>>", lambda e: self._hint_sel())
            self.menu = tk.Menu(root, tearoff=0)
            self.menu.add_command(label="查看内容", command=self._preview)
            self.menu.add_command(label="解密此项", command=self._decrypt_from_list)
            self.menu.add_command(label="导出为…", command=self._export_as)
            self.menu.add_separator()
            self.menu.add_command(label="从列表移除", command=self._remove_sel)
            self.menu.add_command(label="清空列表（销毁全部）", command=self._clear_all)
            self.tree.bind("<Button-3>", self._popup_menu)

            self.drag_ok = False
            if dnd:
                try:
                    root.tk.call("tkdnd::drag_source", "register", self.tree,
                                 DND_FILES)
                    self.tree.bind("<<DragInitCmd>>", self._drag_init)
                    self.tree.bind("<<DragEndCmd>>", lambda *a: None)
                    self.drag_ok = True
                except Exception:
                    self.drag_ok = False

            # ---------- 底部日志 ----------
            logf = tk.Frame(root, bg=BG)
            logf.pack(fill="x", padx=12, pady=(0, 8))
            self.log = tk.Text(logf, height=4, font=(FONT, 9), bg=CARD, fg=DARK,
                               relief="flat", state="disabled", wrap="word")
            self.log.pack(fill="x")
            self.log.tag_configure("err", foreground=ERR)
            self.log.tag_configure("ok", foreground=OK)
            if not self.drag_ok and dnd:
                self._log("拖出引擎不可用：请用右键「导出为…」保存结果", "err")
            elif not dnd:
                self._log("未安装 tkinterdnd2：无法拖入/拖出，请用点击选择与右键导出", "err")

            root.after(80, self._poll)

        # ---------- 基础 UI ----------

        def _set_drop_bg(self, hover):
            self.drop.configure(bg="#dbeafe" if hover else "#ffffff",
                                highlightthickness=1,
                                highlightbackground=ACCENT if hover else "#cbd5e1",
                                highlightcolor=ACCENT if hover else "#cbd5e1")

        def _mode_changed(self):
            need = self.mode_var.get() in ("pass", "hybrid")
            if need:
                self.pwcard.pack(fill="x", pady=(0, 8), ipady=8,
                                 before=self.drop)
            else:
                self.pwcard.pack_forget()

        def _pw_hint_update(self):
            bits = entropy_bits(self.pw_var.get())
            if not self.pw_var.get():
                self.pw_hint.config(text="", fg=DIM)
            elif bits < 40:
                self.pw_hint.config(text=f"≈{bits:.0f} bit · 偏弱，建议 4 个以上随机词或 16 位混合", fg=ERR)
            elif bits < 64:
                self.pw_hint.config(text=f"≈{bits:.0f} bit · 一般", fg="#d97706")
            elif bits < 80:
                self.pw_hint.config(text=f"≈{bits:.0f} bit · 良好", fg=ACCENT)
            else:
                self.pw_hint.config(text=f"≈{bits:.0f} bit · 强", fg=OK)

        def _log(self, msg, tag=None):
            self.log.configure(state="normal")
            self.log.insert("end", msg + "\n", (tag,) if tag else ())
            self.log.see("end")
            self.log.configure(state="disabled")

        def _hint_sel(self):
            n = len(self.tree.selection())
            if n:
                self.status.config(text=f"已选中 {n} 项 — 可拖到资源管理器导出")

        # ---------- 列表管理 ----------

        def _add_item(self, name, data, kind, mode, pair=None):
            item = VirtualItem(_uq_name(name, self._used_names), data, kind,
                               mode, pair)
            self._seq += 1
            item.iid = f"i{self._seq}"
            self.items[item.iid] = item
            self.tree.insert("", "end", iid=item.iid, values=(
                item.name, KIND_NAME[kind],
                MODE_NAME.get(mode, "—"), human_size(len(data))))
            return item

        def _remove_sel(self):
            for iid in self.tree.selection():
                it = self.items.pop(iid, None)
                if it and it.pair and it.pair.iid in self.items:
                    it.pair.pair = None
                    self._log(f"已移除 {it.name}（配对钥匙仍保留）")
                self.tree.delete(iid)
            self.status.config(text=f"列表剩余 {len(self.items)} 项")

        def _clear_all(self):
            if not self.items:
                return
            if messagebox.askokcancel("清空列表", f"将销毁全部 {len(self.items)} 项内存结果（未导出的将丢失）。"):
                self.items.clear()
                self._used_names.clear()
                for i in self.tree.get_children():
                    self.tree.delete(i)
                self.status.config(text="列表已清空，内存结果已销毁")
                self._log("已销毁全部内存结果")

        def _selected_items(self):
            return [self.items[i] for i in self.tree.selection()
                    if i in self.items]

        # ---------- 拖出 / 导出 ----------

        def _drag_init(self, *args):
            """tkdnd 拖出回调：此刻才把内存结果写成临时文件。"""
            try:
                iids = self.tree.selection()
                if not iids:
                    return ""
                paths = []
                for iid in iids:
                    it = self.items.get(iid)
                    if it:
                        paths.append(self.temp.write(it.name, it.data))
                return (("DND_Files",), "copy", paths)
            except Exception as e:
                self._log(f"拖出失败：{e}", "err")
                return ""

        def _export_as(self):
            sel = self._selected_items()
            if not sel:
                return
            for it in sel:
                p = filedialog.asksaveasfilename(
                    initialfile=it.name, parent=root,
                    title="导出结果")
                if not p:
                    continue
                try:
                    with open(p, "wb") as f:
                        f.write(it.data)
                    self._log(f"已导出 {it.name} → {p}", "ok")
                except OSError as e:
                    self._log(f"导出失败 {it.name}: {e}", "err")
            self.status.config(text="导出完成")

        def _popup_menu(self, event):
            if self.tree.identify_row(event.y):
                self.tree.selection_set(self.tree.identify_row(event.y))
                self.menu.tk_popup(event.x_root, event.y_root)

        # ---------- 预览 ----------

        def _preview(self):
            sel = self._selected_items()
            if not sel:
                return
            it = sel[0]
            win = tk.Toplevel(root)
            win.title(f"预览 — {it.name}")
            win.geometry("720x480")
            win.configure(bg=BG)
            txt = tk.Text(win, font=("Consolas", 10), wrap="none",
                          bg="white", relief="flat")
            txt.pack(fill="both", expand=True, padx=8, pady=8)
            txt.insert("1.0", self._preview_text(it))
            txt.configure(state="disabled")

        @staticmethod
        def _preview_text(it):
            if it.kind == "key":
                try:
                    return json.dumps(json.loads(it.data.decode("utf-8")),
                                      ensure_ascii=False, indent=2)
                except Exception:
                    return it.data[:2000].decode("utf-8", errors="replace")
            data = it.data
            try:
                s = data.decode("utf-8")
                printable = sum(1 for c in s if c.isprintable() or c in "\n\r\t")
                if printable / max(len(s), 1) > 0.8:
                    head = s[:6000]
                    note = "\n\n…（已截断）" if len(s) > 6000 else ""
                    tag = "明文内容" if it.kind == "plain" else "容器内容（文本型）"
                    return f"［{tag}］\n{head}{note}"
            except UnicodeDecodeError:
                pass
            rows = []
            for off in range(0, min(len(data), 256), 16):
                chunk = data[off:off + 16]
                hexs = " ".join(f"{b:02x}" for b in chunk)
                asc = "".join(chr(b) if 32 <= b < 127 else "." for b in chunk)
                rows.append(f"{off:06x}  {hexs:<47}  {asc}")
            more = f"\n…（共 {len(data)} 字节）" if len(data) > 256 else ""
            return "［二进制内容 · 前 256 字节］\n" + "\n".join(rows) + more

        # ---------- 拖入处理 ----------

        def _choose_files(self):
            paths = filedialog.askopenfilenames(title="选择文件")
            if paths:
                self._handle_paths(list(paths))

        def _on_drop(self, event):
            try:
                paths = list(root.tk.splitlist(event.data))
            except Exception:
                paths = [event.data]
            self._handle_paths(paths)

        def _handle_paths(self, paths):
            if self.busy:
                self.status.config(text="上一个任务还在处理中，请稍候…")
                return
            locks, containers = [], []
            for p in paths:
                if os.path.isdir(p):
                    self._log(f"跳过文件夹：{p}（请拖入文件）", "err")
                    continue
                mode = sniff_container(p)
                if mode:
                    containers.append((p, mode))
                else:
                    if p.lower().endswith(".key"):
                        self._log(f"钥匙文件需配合容器使用：请拖入 .gcop / .hx 容器", "err")
                        continue
                    locks.append(p)
            if locks:
                self._start_lock(locks)
            for p, mode in containers:
                self._start_disk_decrypt(p, mode)

        # ---------- 混淆（工作线程） ----------

        def _start_lock(self, paths):
            mode = self.mode_var.get()
            pw = None
            if mode in ("pass", "hybrid"):
                pw = self.pw_var.get()
                if not pw:
                    self.status.config(text="请先输入口令（当前模式需要口令）")
                    self._log("混淆取消：当前模式需要口令", "err")
                    return
            jobs = []
            for p in paths:
                try:
                    with open(p, "rb") as f:
                        jobs.append((p, f.read()))
                except OSError as e:
                    self._log(f"读取失败 {p}: {e}", "err")
            if not jobs:
                return
            self.busy = True
            self.status.config(text=f"正在混淆 {len(jobs)} 个文件（{MODE_NAME[mode]}）…")
            base = os.path.basename

            def work():
                results = []
                for p, data in jobs:
                    try:
                        pieces = obfuscate_bytes(data, mode, pw)
                        src = base(p)
                        results.append({"ok": True, "src": src, "pieces": pieces,
                                        "mode": mode})
                    except Exception as e:
                        results.append({"ok": False, "src": base(p),
                                        "err": f"{type(e).__name__}: {e}"})
                self._q.put(("lock", results))

            threading.Thread(target=work, daemon=True).start()

        def _finish_lock(self, results):
            ok = fail = 0
            for r in results:
                if not r["ok"]:
                    fail += 1
                    self._log(f"✗ 混淆失败 {r['src']}: {r['err']}", "err")
                    continue
                ok += 1
                mode = r.get("mode") or self.mode_var.get()
                base = r["src"]
                made = []
                for kind, blob, suffix in r["pieces"]:
                    if kind == "container":
                        made.append(self._add_item(base + suffix, blob,
                                                   "container", mode))
                    else:
                        made.append(self._add_item(base + suffix, blob, "key",
                                                   mode))
                if len(made) == 2:
                    made[0].pair, made[1].pair = made[1], made[0]
                kind_txt = "容器 + 钥匙" if len(made) == 2 else "容器"
                self._log(f"✓ [{MODE_NAME[mode]}] {base} → {kind_txt}（在右侧列表）", "ok")
                if mode in ("key", "hybrid"):
                    self._log("提醒：钥匙也在列表中——需要长期保存时，请把容器和钥匙分开拖出存放", None)
            self.status.config(
                text=f"混淆完成（成功 {ok}，失败 {fail}）— 可继续拖入")
            self.busy = False

        # ---------- 解密 ----------

        def _sidecar_path(self, container_path):
            return container_path + ".key"

        def _start_disk_decrypt(self, path, mode):
            """拖入磁盘上的容器：找旁挂钥匙 → 弹对话框 → 工作线程解密。"""
            side = self._sidecar_path(path)
            key_state = "auto" if os.path.exists(side) else "browse"
            if mode == "pass":
                dlg = DecryptDialog(root, f"解密 {os.path.basename(path)}（口令模式）",
                                    True, "none", "")
            else:
                dlg = DecryptDialog(
                    root, f"解密 {os.path.basename(path)}（{MODE_NAME[mode]}）",
                    mode == "hybrid", key_state,
                    side if key_state == "auto" else "")
            if not dlg.result:
                return
            key_path = None
            if mode in ("key", "hybrid"):
                if key_state == "auto":
                    key_path = side
                else:
                    key_path = dlg.result.get("key_path")
                    if not key_path:
                        self._log("解密取消：未提供钥匙", "err")
                        return
            self._run_decrypt(os.path.basename(path), path, mode,
                              dlg.result["pw"], key_path,
                              external_key=(mode == "key" and key_state == "browse"))

        def _decrypt_from_list(self):
            """右键解密列表中的容器：优先使用配对钥匙。"""
            sel = [it for it in self._selected_items() if it.kind == "container"]
            if not sel:
                self.status.config(text="请选择容器项（容器 / .vx / .hx）再解密")
                return
            it = sel[0]
            mode = it.mode
            pair = it.pair if (it.pair and it.pair.iid in self.items) else None
            key_bytes = pair.data if pair else None
            if mode == "key":
                if key_bytes is None:
                    dlg = DecryptDialog(root, f"解密 {it.name}（钥匙模式）",
                                        False, "browse", "")
                    if not dlg.result or not dlg.result.get("key_path"):
                        return
                    try:
                        with open(dlg.result["key_path"], "rb") as f:
                            key_bytes = f.read()
                    except OSError as e:
                        self._log(f"钥匙读取失败：{e}", "err")
                        return
                self._run_decrypt(it.name, None, "key", None, None,
                                  key_bytes=key_bytes, container_item=it,
                                  external_key=(key_bytes is not None and pair is None))
            elif mode == "pass":
                dlg = DecryptDialog(root, f"解密 {it.name}（口令模式）", True,
                                    "none", "")
                if not dlg.result:
                    return
                self._run_decrypt(it.name, None, "pass", dlg.result["pw"], None,
                                  container_item=it)
            else:
                if key_bytes is None:
                    dlg = DecryptDialog(root, f"解密 {it.name}（混合模式）", True,
                                        "browse", "")
                    if not dlg.result:
                        return
                    if not dlg.result.get("key_path"):
                        self._log("解密取消：混合模式需要钥匙", "err")
                        return
                    try:
                        with open(dlg.result["key_path"], "rb") as f:
                            key_bytes = f.read()
                    except OSError as e:
                        self._log(f"钥匙读取失败：{e}", "err")
                        return
                    pw = dlg.result["pw"]
                else:
                    dlg = DecryptDialog(root, f"解密 {it.name}（混合模式 · 钥匙已配对）",
                                        True, "auto", "")
                    if not dlg.result:
                        return
                    pw = dlg.result["pw"]
                self._run_decrypt(it.name, None, "hybrid", pw, None,
                                  key_bytes=key_bytes, container_item=it)

        def _run_decrypt(self, display_name, disk_path, mode, pw, key_path,
                         key_bytes=None, container_item=None, external_key=False):
            """工作线程执行解密。disk_path 与 container_item 二选一。"""
            self.busy = True
            self.status.config(text=f"正在解密 {display_name} …")

            def work():
                nonlocal key_bytes
                try:
                    if container_item is not None:
                        container = container_item.data
                    else:
                        with open(disk_path, "rb") as f:
                            container = f.read()
                    if key_bytes is None and key_path:
                        with open(key_path, "rb") as f:
                            key_bytes = f.read()
                    key_obj = load_key_obj(key_bytes) if (
                        mode in ("key", "hybrid") and key_bytes) else None
                    plain = restore_bytes(container, mode, pw, key_obj)
                    self._q.put(("decrypt", {"ok": True, "src": display_name,
                                             "plain": plain, "mode": mode,
                                             "external_key": external_key}))
                except Exception as e:
                    self._q.put(("decrypt", {"ok": False, "src": display_name,
                                             "err": f"{type(e).__name__}: {e}"}))

            threading.Thread(target=work, daemon=True).start()

        def _finish_decrypt(self, r):
            self.busy = False
            if not r["ok"]:
                self._log(f"✗ 解密失败 {r['src']}: {r['err']}", "err")
                self.status.config(text="解密失败 — 详见日志")
                return
            base = r["src"]
            for suf in (".gcop", ".vx", ".hx"):
                if base.lower().endswith(suf):
                    base = base[: -len(suf)]
                    break
            self._add_item(base, r["plain"], "plain", r["mode"])
            self._log(f"✓ 已解密 {r['src']} → {base}（在右侧列表，未写盘）", "ok")
            if r["mode"] == "key" and r.get("external_key"):
                self._log("提示：钥匙模式容器无完整性校验——若钥匙与容器不匹配，"
                          "会得到乱码而不是报错（原文不会泄露）", None)
            self.status.config(text="解密完成 — 可继续拖入")

        # ---------- 队列轮询 / 关闭 ----------

        def _poll(self):
            try:
                while True:
                    kind, payload = self._q.get_nowait()
                    if kind == "lock":
                        self._finish_lock(payload)
                    else:
                        self._finish_decrypt(payload)
            except queue.Empty:
                pass
            root.after(80, self._poll)

        def _close(self):
            n = len(self.items)
            if n:
                if not messagebox.askokcancel(
                        "关闭工作台",
                        f"列表中还有 {n} 项结果仅存于内存中，\n关闭程序即全部销毁（未导出的内容无法找回）。\n\n确定关闭？"):
                    return
            self.temp.cleanup()
            root.destroy()

    app = StudioApp()
    root._app = app          # 挂载到窗口对象，供测试与调试访问
    root.mainloop()
    app.temp.cleanup()


if __name__ == "__main__":
    run_gui()
