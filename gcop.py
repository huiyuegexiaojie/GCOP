#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
gcop.py — GCOP 自动混淆/还原工具（v2 加固版）

数学来源：《循环轨道置换（COP/GCOP）：闭式逆变换、循环结构与生成置换群》
只实现论文定义 2（GCOP）。无口令、无密钥派生、无文件头、无校验字段，
输出就是纯粹的置换结果（v2 起带自动填充，密文略大于原文）。

自动混淆 + 自动还原（v2 起整合还原）：
  python gcop.py                          # 打开 GUI 窗口：拖入文件即可混淆（推荐日常使用）
  python gcop.py <file> [file2 ...]       # 命令行模式：混淆一个或多个文件
  python gcop.py <file.gcop>              # 还原：.gcop 输入自动进还原模式（找同目录 .key）
  python gcop.py <file> -o out.gcop       # 指定输出路径（单文件）
  python gcop.py <file> -f                # 允许覆盖已存在的输出（混淆/还原通用）
  也可以直接把文件拖到 gcop-gui.bat 图标上：拖普通文件=混淆，拖 .gcop=还原

行为：
  - 每个输入文件生成 <file>.gcop（混淆结果，v2 起会自动填充到 16 字节对齐、
    最短 128 字节并随机追加 0~2 块，故密文大于原文）与 <file>.gcop.key（还原钥匙，JSON）
  - 输入 .gcop 文件时自动还原：读取同目录 .key，还原为去掉 .gcop 后缀的原文件名；
    目标已存在时拒绝覆盖（-f 强制）；兼容 v1 旧钥匙（无 pad 字段按 0 处理）
  - 文本文件（UTF-8 可解码）直接把混淆后的文本打印到 stdout；二进制文件只打印输出路径
  - 不显示任何混淆参数（防泄露）；还原所需的全部信息只存在于 .key 中，请分开保管

加固策略 v2（相对 v1，依据 2026-10 第二轮逆向评估）：
  - **自动填充到合数长度**：混淆前把文件填充到 16 字节块对齐、最短 128 字节，
    并随机追加 0~2 个额外块模糊长度指纹；填充字节取自 os.urandom。
    彻底消灭质数长度的 g=1 仿射退化（该档位已被实测无钥匙秒级破译）
  - g 下限 4 → 8：消灭 g=2/3/4 的小参数空间档（g=4 时全空间仅 ~2^40）；
    填充保证 16 | n'，因此 [8, n'/2] 区间恒有真因子，g=1 回退路径不再可达
  - rounds 从 [8, 24] 随机，并拒绝低阶退化（沿用 v1）
  - g 上限 1024，保持 .key 紧凑
  - .key 升级 version 2：新增 "pad" 字段记录填充长度，还原后按此裁剪
  - 空文件 / 单字节文件不再直通：同样填充+混淆（v1 中它们完全不设防）

诚实定位（论文 9.4 节）: 纯位置置换混淆，不改变字节值与频率分布，
不是密码学意义上的加密；一对同长度已知明文即可恢复密钥。
"""

import argparse
import json
import os
import random
import sys
from math import gcd


class ParamError(Exception):
    pass


# ---------------------------------------------------------------------------
# 核心映射（定义 2；读索引约定 out[w] = in[map[w]]）
#   GCOP 正向:  Y[r*L + j] = X[sigma[r] + g*((a[r] + q[r]*j) mod L)],   L = n // g
# ---------------------------------------------------------------------------

def gcop_map_fwd(n: int, g: int, sigma, a, q):
    """GCOP 正向读索引表（游走式建表，与闭式公式等价）。"""
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


def _composite_map(n: int, g: int, sigma, a, q, rounds: int):
    """rounds 次复合后的总读索引表（等价于逐轮施加，一次性 O(rounds*n)）。"""
    base = gcop_map_fwd(n, g, sigma, a, q)
    m = list(range(n))
    for _ in range(rounds):
        m = [base[x] for x in m]
    return m


def gcop_obfuscate(data: bytes, g: int, sigma, a, q, rounds: int) -> bytes:
    """混淆：直接用复合映射一次性置换。"""
    m = _composite_map(len(data), g, sigma, a, q, rounds)
    return bytes(map(data.__getitem__, m))


def gcop_restore(cipher: bytes, K: dict) -> bytes:
    """还原：按 .key 重建读索引表并散射还原；v2 钥匙按 "pad" 裁掉尾部填充。

    兼容 v1（无 pad 字段）与 v2 钥匙。密文长度与钥匙不符时抛 ParamError。
    """
    n = K["n"]; g = K["g"]
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


# ---------------------------------------------------------------------------
# 强化参数生成
# ---------------------------------------------------------------------------

KEY_TYPE = "gcop-key"
KEY_VERSION = 2
_AUTO_G_CAP = 1024      # g 上限，保持 .key 紧凑
_G_FLOOR = 8            # 安全下限：g<8 的档位参数空间过小（g=4 全空间 ~2^40）
_ROUNDS_LO, _ROUNDS_HI = 8, 24
_IDENTITY_CHECK_LIMIT = 1 << 16   # 复合置换恒等校验的文件规模上限
_PAD_BLOCK = 16         # 填充对齐块：16 | n' 保证存在 g>=8 的真因子
_PAD_MIN = 128          # 最短混淆长度：消灭极短文件的参数全枚举档
_PAD_RAND_EXTRA = 2     # 额外随机追加 0~2 块，模糊长度指纹


def pad_for_obfuscation(data: bytes, rng=None) -> tuple:
    """v2: 混淆前填充。返回 (填充后字节串, pad 长度)。

    - 对齐到 16 字节块且总长 >= 128，另随机追加 0~2 块模糊真实长度；
    - 填充字节取 os.urandom（不可预测，避免零填充的统计指纹）；
    - 16 | n' 且 n' >= 128 保证 [8, n'/2] 区间恒有真因子，
      auto_generate_params 永不落入 g=1 仿射档。
    """
    rng = rng or random.SystemRandom()
    n = len(data)
    blocks = -(-max(n, 1) // _PAD_BLOCK)
    target = max(_PAD_MIN, blocks * _PAD_BLOCK) + _PAD_BLOCK * rng.randint(0, _PAD_RAND_EXTRA)
    pad = target - n
    if pad <= 0:
        return data, 0
    return data + os.urandom(pad), pad


def _proper_divisors(n: int):
    """n 的全部真因子（1 <= d < n）。"""
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


def _random_coprime(rng, L: int) -> int:
    while True:
        c = rng.randint(1, L - 1)
        if gcd(c, L) == 1:
            return c


def _is_degenerate(g: int, sigma, a, q) -> bool:
    """全默认组合（sigma=恒置, a=0, q=1）构成低阶对合，高偶数次幂会回到恒等。"""
    return (sigma == list(range(g)) and not any(a) and all(x == 1 for x in q))


def auto_generate_params(n: int, rng=None):
    """随机生成一组强化 GCOP 参数 (g, sigma, a, q, rounds)。

    - g 从 [G_FLOOR=8, min(n//2, CAP)] 的真因子中随机选一个（保持跨文件多样性）。
      v2 填充保证 16 | n' 且 n' >= 128，因此该区间恒有真因子（8 必为因子），
      无候选回退与 g=1 仿射档在正常流程下不可达（保留代码仅作安全网）。
    - rounds ∈ [8, 24]；并做防退化校验。
    """
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
        # 概率极低（sigma=恒置 且 a 全 0 且 q 全 1），直接重抽一轮参数
        return auto_generate_params(n, rng)

    # 小文件：完整校验复合置换非恒等；大文件：退化组合已在上面排除，
    # 随机 sigma/a/q 下高次幂为恒等的概率可忽略，省去 O(rounds*n) 校验
    if n <= _IDENTITY_CHECK_LIMIT:
        m = _composite_map(n, g, sigma, a, q, rounds)
        if m == list(range(n)):
            return auto_generate_params(n, rng)
    return g, sigma, a, q, rounds


def save_key(path: str, n: int, g: int, sigma, a, q, rounds: int, pad: int = 0) -> None:
    obj = {"type": KEY_TYPE, "version": KEY_VERSION, "n": n, "g": g, "pad": pad,
           "sigma": list(sigma), "a": list(a), "q": list(q), "rounds": rounds}
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f)


# ---------------------------------------------------------------------------
# 命令行
# ---------------------------------------------------------------------------

def _looks_like_text(b: bytes) -> bool:
    """无 NUL、无控制字符（除 \\t \\r \\n）即按文本输出。
    注意：中文字节被置换后必然不再是合法 UTF-8，因此不能用 UTF-8 解码成功与否来判定。"""
    if not b or b"\x00" in b:
        return False
    return all(ch == 9 or ch == 10 or ch == 13 or 32 <= ch != 127 for ch in b)


def _emit_result(out_path: str, out_data: bytes, key_path: str or None) -> None:
    """文本文件把混淆后的原始字节直接写 stdout（不做任何编码转换，忠实呈现）；
    二进制文件只报输出路径。最后单独一行报 .key 位置。"""
    if _looks_like_text(out_data):
        sys.stdout.buffer.write(out_data)
        if not out_data.endswith(b"\n"):
            sys.stdout.buffer.write(b"\n")
        sys.stdout.buffer.flush()
    else:
        print(f"输出: {out_path}")
    if key_path:
        print(f"key: {key_path}")


def _restore_file(path: str, force: bool) -> bool:
    """CLI 还原：path 必须是 .gcop，钥匙取同目录 <path>.key。"""
    if len(path) <= 5 or not path.lower().endswith(".gcop"):
        print(f"error: 还原模式需要 .gcop 文件: {path}", file=sys.stderr)
        return False
    key_path = path + ".key"
    if not os.path.exists(key_path):
        print(f"error: 找不到钥匙 {key_path}（还原需要与之配对的 .key）", file=sys.stderr)
        return False
    try:
        with open(key_path, "r", encoding="utf-8") as f:
            K = json.load(f)
        with open(path, "rb") as f:
            cipher = f.read()
    except (OSError, json.JSONDecodeError) as e:
        print(f"error: 钥匙/密文读取失败: {e}", file=sys.stderr)
        return False
    out_path = path[:-5]
    if os.path.exists(out_path) and not force:
        print(f"error: {out_path} 已存在，拒绝覆盖（-f 强制覆盖）", file=sys.stderr)
        return False
    try:
        plain = gcop_restore(cipher, K)
    except (ParamError, KeyError, ValueError) as e:
        print(f"error: 还原失败: {e}", file=sys.stderr)
        return False
    with open(out_path, "wb") as f:
        f.write(plain)
    _emit_result(out_path, plain, None)
    return True


def _process_file(path: str, out_path: str or None, force: bool) -> bool:
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError as e:
        print(f"error: 无法读取 {path}: {e}", file=sys.stderr)
        return False

    n = len(data)
    if out_path is None:
        out_path = path + ".gcop"
    key_path = out_path + ".key"

    explicit = args_explicit_out is not None and out_path == args_explicit_out
    allowed = force or explicit or not os.path.exists(out_path)
    # 说明：显式 -o 或 -f 时允许覆盖；默认输出路径已存在且未加 -f 时拒绝
    if not allowed:
        print(f"error: {out_path} 已存在，拒绝覆盖（-f 强制覆盖）", file=sys.stderr)
        return False

    # v2: 统一填充流程 —— 空文件/单字节文件也不再直通
    padded, pad = pad_for_obfuscation(data)
    g, sigma, a, q, rounds = auto_generate_params(len(padded))
    out_data = gcop_obfuscate(padded, g, sigma, a, q, rounds)
    with open(out_path, "wb") as f:
        f.write(out_data)
    save_key(key_path, len(padded), g, sigma, a, q, rounds, pad)
    _emit_result(out_path, out_data, key_path)
    return True


# ---------------------------------------------------------------------------
# GUI（无参数启动时打开：拖入 / 选择文件 → 混淆 → 结果直接显示在窗口里）
# ---------------------------------------------------------------------------

class _GuiApp:
    """拖入即混淆的轻量窗口。依赖 tkinter（系统 Python 自带）；
    拖拽能力依赖 tkinterdnd2（缺失时退化为点击选择，窗口内会提示安装命令）。"""

    # ---- 视觉常量 ----
    C_BG = "#eef2f8"; C_CARD = "#ffffff"; C_LINE = "#d5deeb"
    C_TEXT = "#1f2937"; C_SUB = "#8a94a6"; C_BODY = "#33415c"
    C_ACC = "#3b82f6"; C_ACC_DK = "#1d4ed8"; C_HOT_BG = "#f2f8ff"
    C_OK = "#16a34a"; C_ERR = "#dc2626"; C_ACC2 = "#7c3aed"

    def __init__(self, root):
        self.root = root
        self.busy = False
        self.last_dir = os.getcwd()
        import queue
        self._q = queue.Queue()   # 工作线程 → 主线程 的结果队列（tkinter 线程安全惯例）
        self._alive = True

        root.title("GCOP 混淆工作台")
        root.geometry("780x580")
        root.minsize(660, 500)
        root.configure(bg=self.C_BG)
        root.protocol("WM_DELETE_WINDOW", self._close)

        has_dnd = True
        try:
            from tkinterdnd2 import DND_FILES
            root.drop_target_register(DND_FILES)
            root.dnd_bind("<<Drop>>", self._on_drop)
        except Exception:
            has_dnd = False
        self.has_dnd = has_dnd

        import tkinter as tk
        self._tk = tk

        # ---- 顶栏 ----
        head = tk.Frame(root, bg=self.C_BG)
        head.pack(fill="x", padx=20, pady=(16, 10))
        tk.Label(head, text="GCOP 混淆工作台", font=("Microsoft YaHei UI", 16, "bold"),
                 fg=self.C_TEXT, bg=self.C_BG).pack(side="left")
        tk.Label(head, text="v2 · 循环轨道置换", font=("Microsoft YaHei UI", 9),
                 fg=self.C_SUB, bg=self.C_BG).pack(side="left", padx=(10, 0), pady=(7, 0))

        # ---- 拖放区 ----
        drop_text = ("🔐  拖入文件 → 立即混淆        拖入 .gcop → 自动还原\n\n或点击此处选择文件"
                     if has_dnd else
                     "点击此处选择文件（混淆与还原通用）\n\n拖拽引擎未安装，可选装: pip install tkinterdnd2")
        self.drop = tk.Label(
            root, text=drop_text, justify="center",
            font=("Microsoft YaHei UI", 12),
            fg=self.C_BODY, bg=self.C_CARD, cursor="hand2",
            highlightthickness=2, highlightbackground=self.C_LINE, highlightcolor=self.C_ACC,
        )
        self.drop.pack(fill="x", padx=20, pady=(0, 12), ipady=24)
        self.drop.bind("<Button-1>", lambda e: self.choose_files())
        self.drop.bind("<Enter>", lambda e: self._drop_style(self.C_HOT_BG, self.C_ACC, self.C_ACC_DK))
        self.drop.bind("<Leave>", lambda e: self._drop_style(self.C_CARD, self.C_LINE, self.C_BODY))

        # ---- 结果区 ----
        from tkinter import scrolledtext
        self.out = scrolledtext.ScrolledText(
            root, font=("Microsoft YaHei UI", 10), state="disabled", wrap="word",
            bg=self.C_CARD, fg=self.C_TEXT, relief="flat", bd=0,
            highlightthickness=1, highlightbackground=self.C_LINE,
            padx=14, pady=10, insertbackground=self.C_TEXT)
        self.out.pack(fill="both", expand=True, padx=20, pady=(0, 12))
        self.out.tag_configure("title", foreground=self.C_TEXT,
                               font=("Microsoft YaHei UI", 10, "bold"))
        self.out.tag_configure("acc", foreground=self.C_ACC)
        self.out.tag_configure("acc2", foreground=self.C_ACC2)
        self.out.tag_configure("ok", foreground=self.C_OK)
        self.out.tag_configure("err", foreground=self.C_ERR)
        self.out.tag_configure("dim", foreground=self.C_SUB)

        # ---- 状态栏 ----
        bar = tk.Frame(root, bg=self.C_BG)
        bar.pack(fill="x", padx=20, pady=(0, 14))
        hint = ("就绪 —— 拖入文件混淆，拖入 .gcop 还原" if has_dnd else
                "就绪 —— 拖拽引擎未安装，点击上方区域选择文件；安装后可拖入: pip install tkinterdnd2")
        self.status = tk.Label(bar, text=hint, anchor="w", fg=self.C_SUB,
                               bg=self.C_BG, font=("Microsoft YaHei UI", 9))
        self.status.pack(side="left", fill="x", expand=True)
        self._mkbtn(bar, "📂 打开文件夹", self.open_folder)
        self._mkbtn(bar, "🧹 清空", self.clear, padx=(0, 8))

        self.root.after(80, self._poll)   # 主线程轮询结果队列

    def _drop_style(self, bg, border, fg):
        """拖放区悬浮/离开时的配色切换。"""
        try:
            self.drop.configure(bg=bg, highlightbackground=border,
                                highlightcolor=border, fg=fg)
        except Exception:
            pass

    def _mkbtn(self, parent, text, cmd, padx=(8, 0)):
        """扁平按钮（Label 实现），带悬浮变色。"""
        b = self._tk.Label(parent, text=text, font=("Microsoft YaHei UI", 9),
                           fg=self.C_BODY, bg=self.C_CARD, cursor="hand2",
                           highlightthickness=1, highlightbackground=self.C_LINE,
                           padx=12, pady=5)
        b.pack(side="right", padx=padx)
        b.bind("<Enter>", lambda e: b.configure(bg=self.C_HOT_BG, fg=self.C_ACC_DK))
        b.bind("<Leave>", lambda e: b.configure(bg=self.C_CARD, fg=self.C_BODY))
        b.bind("<Button-1>", lambda e: cmd())
        return b

    def _poll(self):
        """主线程定期取队列结果并渲染（线程安全；tkinter 控件禁止跨线程操作）。"""
        if not self._alive:
            return
        try:
            import queue
            try:
                while True:
                    results = self._q.get_nowait()
                    self._done(results)
            except queue.Empty:
                pass
        except self._tk.TclError:
            return   # 窗口已销毁，停止轮询
        self.root.after(80, self._poll)

    def _close(self):
        self._alive = False
        self.root.destroy()

    # ---- 界面动作 ----
    def choose_files(self):
        from tkinter import filedialog
        paths = filedialog.askopenfilenames(title="选择要混淆的文件")
        paths = [str(p) for p in paths if str(p)]
        if paths:
            self.process(paths)

    def _on_drop(self, event):
        paths = [str(p) for p in self.root.tk.splitlist(event.data) if str(p)]
        if paths:
            self.process(paths)

    def clear(self):
        self.out.configure(state="normal")
        self.out.delete("1.0", "end")
        self.out.configure(state="disabled")

    def open_folder(self):
        try:
            os.startfile(self.last_dir)   # Windows
        except Exception:
            self.append(f"无法打开文件夹: {self.last_dir}\n", "err")

    def append(self, text, tag=None):
        self.out.configure(state="normal")
        if tag:
            self.out.insert("end", text, tag)
        else:
            self.out.insert("end", text)
        self.out.configure(state="disabled")
        self.out.see("end")

    # ---- 处理流程（后台线程，避免大文件卡界面）----
    def process(self, paths):
        if self.busy:
            self.append("上一个批次还在处理中，请稍候…\n", "dim")
            return
        self.busy = True
        self.status.config(text="处理中…")
        import threading

        def work():
            results = []
            for p in paths:
                try:
                    if p.lower().endswith(".gcop"):
                        results.append(self.restore_one(p))
                    else:
                        results.append(self.obfuscate_one(p))
                except Exception as e:
                    results.append({"src": p, "err": f"{type(e).__name__}: {e}"})
            self._q.put(results)   # 投递给主线程渲染（不在子线程碰 tkinter）

        threading.Thread(target=work, daemon=True).start()

    def _done(self, results):
        n_ok = n_err = 0
        for r in results:
            if r.get("err"):
                n_err += 1
                self.append(f"✗  {os.path.basename(r['src'])}\n", "err")
                self.append(f"    错误  {r['err']}\n\n", "dim")
                continue
            n_ok += 1
            name = os.path.basename(r["src"])
            if r.get("restored"):
                self.append("🔓 已还原  ", "acc2")
            else:
                self.append("🔒 已混淆  ", "acc")
            self.append(f"{name}\n", "title")
            self.append(f"    输出  {r['out']}\n", "dim")
            if r.get("sizes"):
                self.append(f"    体积  {r['sizes']}\n", "dim")
            if r.get("key"):
                self.append(f"    钥匙  {r['key']}\n", "dim")
            if r.get("preview"):
                self.append(f"    预览  {r['preview']}\n", "dim")
            self.append("\n")
        self.busy = False
        summary = []
        if n_ok: summary.append(f"成功 {n_ok}")
        if n_err: summary.append(f"失败 {n_err}")
        self.status.config(text="完成（" + "，".join(summary) + "）—— 可继续拖入文件")
        if results and not results[-1].get("err"):
            self.last_dir = os.path.dirname(os.path.abspath(results[-1]["out"]))

    @staticmethod
    def restore_one(path):
        """GUI 还原：path 为 .gcop，钥匙取同目录 <path>.key。"""
        keyp = path + ".key"
        if not os.path.exists(keyp):
            raise ParamError(f"找不到钥匙 {keyp}")
        with open(keyp, "r", encoding="utf-8") as f:
            K = json.load(f)
        with open(path, "rb") as f:
            cipher = f.read()
        outp = path[:-5]
        overwritten = os.path.exists(outp)
        plain = gcop_restore(cipher, K)
        with open(outp, "wb") as f:
            f.write(plain)
        preview = None
        if _looks_like_text(plain):
            preview = plain[:200].decode("latin-1")
            if len(plain) > 200:
                preview += " …"
        sizes = f"{len(cipher)} B → {len(plain)} B"
        if K.get("pad"):
            sizes += f"（剥离填充 {K['pad']} B）"
        return {"src": path, "out": outp, "key": None, "sizes": sizes,
                "preview": preview, "overwritten": overwritten, "restored": True}

    @staticmethod
    def obfuscate_one(path):
        with open(path, "rb") as f:
            data = f.read()
        outp = path + ".gcop"
        overwritten = os.path.exists(outp)
        # v2: 统一填充流程 —— 空文件/单字节文件也不再直通
        padded, pad = pad_for_obfuscation(data)
        g, sigma, a, q, rounds = auto_generate_params(len(padded))
        out_data = gcop_obfuscate(padded, g, sigma, a, q, rounds)
        keyp = outp + ".key"
        with open(outp, "wb") as f:
            f.write(out_data)
        save_key(keyp, len(padded), g, sigma, a, q, rounds, pad)
        preview = None
        if _looks_like_text(out_data):
            preview = out_data[:200].decode("latin-1")
            if len(out_data) > 200:
                preview += " …"
        sizes = f"{len(data)} B → {len(out_data)} B"
        if pad:
            sizes += f"（含填充 {pad} B）"
        return {"src": path, "out": outp, "key": keyp, "sizes": sizes,
                "preview": preview, "overwritten": overwritten}

    def run(self):
        self.root.mainloop()


def _run_gui() -> int:
    try:
        import tkinter as tk
    except ImportError:
        print("error: 当前 Python 没有 tkinter，无法打开 GUI。", file=sys.stderr)
        print("       请用系统 Python 运行，例如: py gcop.py  或  python gcop.py", file=sys.stderr)
        return 2
    try:
        from tkinterdnd2 import TkinterDnD
        root = TkinterDnD.Tk()
    except Exception:
        root = tk.Tk()
    _GuiApp(root).run()
    return 0


# ---------------------------------------------------------------------------
# 命令行
# ---------------------------------------------------------------------------

args_explicit_out = None


def main(argv=None) -> int:
    global args_explicit_out
    if argv is None and len(sys.argv) == 1:
        return _run_gui()
    ap = argparse.ArgumentParser(
        prog="gcop",
        description="GCOP 自动混淆（纯位置置换，非加密）；生成 .gcop 与还原钥匙 .key，"
                    "不显示任何参数",
    )
    ap.add_argument("files", nargs="+", help="输入文件（可多个）")
    ap.add_argument("-o", "--output", help="输出路径（仅单文件时有效；缺省 <file>.gcop）")
    ap.add_argument("-f", "--force", action="store_true", help="覆盖已存在的输出文件")
    args = ap.parse_args(argv)

    if args.output and len(args.files) > 1:
        print("error: -o 只能配合单个输入文件使用", file=sys.stderr)
        return 2
    args_explicit_out = args.output

    ok = True
    for path in args.files:
        if path.lower().endswith(".gcop"):
            # .gcop 输入自动进还原模式（拖拽 / 命令行同一逻辑）
            if not _restore_file(path, args.force):
                ok = False
        elif not _process_file(path, args.output if args.output else None, args.force):
            ok = False
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
