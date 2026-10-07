# -*- coding: utf-8 -*-
"""GCOP 通用解密器 v2（黑盒逆向产物，未读源码）
用法: python universal_decryptor.py <file.gcop> <file.key> [输出文件]
支持: v1 钥匙（无 pad）/ v2 钥匙（自动填充，按 "pad" 裁剪）
"""
import json, sys

def simulate_gather(K, n):
    g = K["g"]; gs = n // g
    if g * gs != n:
        raise ValueError(f"n={n} 不能被 g={g} 整除")
    sigma, a, q, rounds = K["sigma"], K["a"], K["q"], K["rounds"]
    G = list(range(n))
    for _ in range(rounds):
        groups = [[G[j + m*g] for m in range(gs)] for j in range(g)]
        groups = [groups[sigma[j]] for j in range(g)]
        newG = [0]*n
        for j, gb in enumerate(groups):
            for m, v in enumerate(gb):
                newG[j*gs + m] = v
        groups = [newG[j*gs:(j+1)*gs] for j in range(g)]
        groups = [[gb[(a[j] + q[j]*m) % gs] for m in range(gs)] for j, gb in enumerate(groups)]
        G = [x for gb in groups for x in gb]
    return G

def decrypt(C, K):
    G = simulate_gather(K, len(C))
    full = [0]*len(C)
    for m in range(len(C)):
        full[G[m]] = C[m]
    pad = K.get("pad", 0)          # v2: 尾部随机填充
    return bytes(full[:len(C)-pad]) if pad else bytes(full)

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(__doc__); sys.exit(1)
    C = open(sys.argv[1], "rb").read()
    K = json.load(open(sys.argv[2]))
    plain = decrypt(C, K)
    if len(sys.argv) >= 4:
        open(sys.argv[3], "wb").write(plain)
        print(f"[已还原] {sys.argv[3]} ({len(plain)} 字节)")
    else:
        sys.stdout.buffer.write(plain)
