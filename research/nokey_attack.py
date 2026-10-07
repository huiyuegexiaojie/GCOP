# -*- coding: utf-8 -*-
"""无钥匙破译演示: 质数长度文件 (g=1) 退化为仿射密码 -> 暴力枚举 (α, β)
攻击者持有: 仅 sample_test.txt.gcop (643B)。不使用任何 .key 文件。
"""
import os, sys, unicodedata
os.chdir(os.path.dirname(os.path.abspath(__file__)))

C = open("../sample_test.txt.gcop", "rb").read()
n = len(C)
print(f"[*] 密文: {n} 字节; n 是否质数: {all(n % i for i in range(2, int(n**0.5)+1))}")
print(f"[*] 算法已知 -> 质数长度强制 g=1 -> 净变换 = 仿射 S(x)=α·x+β (mod n)")
print(f"[*] 候选空间: n × φ(n) = {n} × {n-1} = {n*(n-1)}")

def score(plain):
    """快速评分: UTF-8 可解码 + 可打印占比"""
    try:
        s = plain.decode("utf-8")
    except UnicodeDecodeError:
        return -1.0
    good = sum(1 for ch in s if ch.isprintable() or ch in "\n\r\t")
    return good / len(s)

# 暴力枚举: plain[x] = C[(α·x + β) mod n]
hits = []
tested = 0
for alpha in range(1, n):
    if alpha == 0: continue
    # α 须与 n 互素才是双射 (n=643 质数 -> 全部 1..642)
    for beta in range(n):
        tested += 1
        # 早停: 先只算前 16 字节
        head = bytes(C[(alpha*x + beta) % n] for x in range(16))
        try:
            head.decode("utf-8")
        except UnicodeDecodeError:
            continue
        plain = bytes(C[(alpha*x + beta) % n] for x in range(n))
        sc = score(plain)
        if sc > 0.95:
            hits.append((alpha, beta, sc, plain))
            print(f"    [命中] α={alpha} β={beta} 可打印率={sc*100:.1f}%")
print(f"[*] 实际测试 {tested} 个候选")

if hits:
    alpha, beta, sc, plain = hits[0]
    print(f"\n[破译成功] 无钥匙还原 sample_test.txt.gcop:")
    print("─" * 56)
    print(plain.decode("utf-8"))
    print("─" * 56)
    truth = open("../sample_test.txt", "rb").read()
    print(f"[比对原文] {'✓ 逐字节一致 — 无钥匙完全破译' if plain == truth else '✗ 与原文不符'}")
else:
    print("[未命中] 仿射假设不适用于该样本")
