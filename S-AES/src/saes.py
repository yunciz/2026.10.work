# -*- coding: utf-8 -*-
"""
S-AES（Simplified AES）加解密系统
================================================================
《信息安全导论》课程作业 2 · S-AES 算法实现

算法标准：教材附录 D 简化 AES（16-bit 分组 / 16-bit 密钥）
模块划分：
    SAESCore   核心加解密算法（纯函数，查表法预计算优化）
    SAESUtils  扩展功能（ASCII 编解码、多重加密、中间相遇攻击、CBC）
    SAESGUI    Tkinter 图形界面（四选项卡布局）

运行：python src/saes.py
================================================================
"""

import datetime
import os
import random
import threading
import time
import tkinter as tk
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from tkinter import messagebox, ttk

# =================================================================
# 1. 算法常量与预计算表
# =================================================================
# S 盒与逆 S 盒（一维数组，下标直接对应半字节 0x0~0xF）
S_BOX = [
    0x9, 0x4, 0xA, 0xB,
    0xD, 0x1, 0x8, 0x5,
    0x6, 0x2, 0x0, 0x3,
    0xC, 0xE, 0xF, 0x7,
]
INV_S_BOX = [
    0xA, 0x5, 0x9, 0xB,
    0x1, 0x7, 0x8, 0xF,
    0x6, 0x0, 0x2, 0x3,
    0xC, 0x4, 0xD, 0xE,
]

RCON = (0x80, 0x30)  # 密钥扩展轮常数

BLOCK_SIZE = 16      # 分组长度（bit）
KEY_SPACE = 1 << 16  # 密钥空间 2^16 = 65536


def _gf_mul_slow(a, b):
    """GF(2^4) 乘法，模多项式 x^4 + x + 1（仅用于启动时建表）。"""
    result = 0
    for _ in range(4):
        if b & 1:
            result ^= a
        high_bit = a & 0x8
        a = (a << 1) & 0xF
        if high_bit:
            a ^= 0x3  # x^4 ≡ x + 1
        b >>= 1
    return result


# 预计算 GF(2^4) 完整乘法表，列混淆直接查表
_GF_MUL = [[_gf_mul_slow(a, b) for b in range(16)] for a in range(16)]
_MUL2 = _GF_MUL[2]
_MUL4 = _GF_MUL[4]
_MUL9 = _GF_MUL[9]


# =================================================================
# 2. 核心算法模块
# =================================================================
class SAESCore:
    """S-AES 核心加解密，所有方法均为无副作用的纯函数。"""

    @staticmethod
    def key_expansion(key_16bit):
        """密钥扩展：16-bit 主密钥 -> 3 个轮密钥 (K0, K1, K2)。"""
        w0, w1 = (key_16bit >> 8) & 0xFF, key_16bit & 0xFF

        def g(word, rcon):
            # RotNib + SubNib + RCON
            n0, n1 = (word >> 4) & 0xF, word & 0xF
            return ((S_BOX[n1] << 4) | S_BOX[n0]) ^ rcon

        w2 = w0 ^ g(w1, RCON[0])
        w3 = w2 ^ w1
        w4 = w2 ^ g(w3, RCON[1])
        w5 = w4 ^ w3
        return (w0 << 8) | w1, (w2 << 8) | w3, (w4 << 8) | w5

    @staticmethod
    def _to_nibbles(block_16bit):
        """16-bit 拆分为 4 个半字节 [s00, s10, s01, s11]（按列读取）。"""
        return [(block_16bit >> 12) & 0xF, (block_16bit >> 8) & 0xF,
                (block_16bit >> 4) & 0xF, block_16bit & 0xF]

    @staticmethod
    def _from_nibbles(nibbles):
        """4 个半字节拼回 16-bit。"""
        return (nibbles[0] << 12) | (nibbles[1] << 8) | (nibbles[2] << 4) | nibbles[3]

    @staticmethod
    def _add_round_key(nibbles, round_key):
        """轮密钥加（AK）。"""
        key_nibbles = SAESCore._to_nibbles(round_key)
        return [s ^ k for s, k in zip(nibbles, key_nibbles)]

    @staticmethod
    def _shift_rows(nibbles):
        """行移位（SR/ISR）：交换第二行的两个半字节，返回新列表。"""
        return [nibbles[0], nibbles[3], nibbles[2], nibbles[1]]

    @staticmethod
    def _mix_columns(nibbles, inverse=False):
        """列混淆（MC/IMC），乘法查表。"""
        s00, s10, s01, s11 = nibbles
        if inverse:
            return [
                _MUL9[s00] ^ _MUL2[s10], _MUL2[s00] ^ _MUL9[s10],
                _MUL9[s01] ^ _MUL2[s11], _MUL2[s01] ^ _MUL9[s11],
            ]
        return [
            s00 ^ _MUL4[s10], _MUL4[s00] ^ s10,
            s01 ^ _MUL4[s11], _MUL4[s01] ^ s11,
        ]

    @staticmethod
    def encrypt_block(plaintext_16bit, key_16bit):
        """单块加密：AK0 -> (NS+SR+MC+AK1) -> (NS+SR+AK2)。"""
        k0, k1, k2 = SAESCore.key_expansion(key_16bit)
        state = SAESCore._to_nibbles(plaintext_16bit)
        state = SAESCore._add_round_key(state, k0)
        state = [S_BOX[n] for n in state]
        state = SAESCore._shift_rows(state)
        state = SAESCore._mix_columns(state)
        state = SAESCore._add_round_key(state, k1)
        state = [S_BOX[n] for n in state]
        state = SAESCore._shift_rows(state)
        state = SAESCore._add_round_key(state, k2)
        return SAESCore._from_nibbles(state)

    @staticmethod
    def decrypt_block(ciphertext_16bit, key_16bit):
        """单块解密：加密的逆运算。"""
        k0, k1, k2 = SAESCore.key_expansion(key_16bit)
        state = SAESCore._to_nibbles(ciphertext_16bit)
        state = SAESCore._add_round_key(state, k2)
        state = SAESCore._shift_rows(state)
        state = [INV_S_BOX[n] for n in state]
        state = SAESCore._add_round_key(state, k1)
        state = SAESCore._mix_columns(state, inverse=True)
        state = SAESCore._shift_rows(state)
        state = [INV_S_BOX[n] for n in state]
        state = SAESCore._add_round_key(state, k0)
        return SAESCore._from_nibbles(state)

    # bit 字符串包装（GUI 直接调用）
    @staticmethod
    def encrypt(plain_bits, key_bits):
        return format(SAESCore.encrypt_block(int(plain_bits, 2), int(key_bits, 2)),
                      '0{}b'.format(BLOCK_SIZE))

    @staticmethod
    def decrypt(cipher_bits, key_bits):
        return format(SAESCore.decrypt_block(int(cipher_bits, 2), int(key_bits, 2)),
                      '0{}b'.format(BLOCK_SIZE))


# =================================================================
# 3. 工具与扩展功能模块
# =================================================================
def _forward_chunk(task):
    """中间相遇攻击前向建表线程任务：枚举 [begin, end) 内的 K1。"""
    begin, end, plaintext = task
    table = defaultdict(list)
    for k1 in range(begin, end):
        middle = SAESCore.encrypt_block(plaintext, k1)
        table[middle].append(k1)
    return table


class SAESUtils:
    # --- 编码转换 ---
    @staticmethod
    def str_to_bin(text):
        return ''.join(format(ord(c), '08b') for c in text)

    @staticmethod
    def bin_to_str(bits):
        chars = [chr(int(bits[i:i + 8], 2)) for i in range(0, len(bits) - 7, 8)]
        return ''.join(chars)

    @staticmethod
    def is_printable(text):
        return bool(text) and all(32 <= ord(ch) < 127 for ch in text)

    # --- 单重 S-AES 字符串 / 长二进制串 ---
    @staticmethod
    def encrypt_bits(bits, key_bits, block=BLOCK_SIZE):
        if len(bits) % block != 0:
            raise ValueError('输入长度必须是 %d 的倍数' % block)
        key = int(key_bits, 2)  # 密钥仅解析一次
        return ''.join(format(SAESCore.encrypt_block(int(bits[i:i + block], 2), key), '016b')
                       for i in range(0, len(bits), block))

    @staticmethod
    def decrypt_bits(bits, key_bits, block=BLOCK_SIZE):
        if len(bits) % block != 0:
            raise ValueError('密文长度必须是 %d 的倍数' % block)
        key = int(key_bits, 2)
        return ''.join(format(SAESCore.decrypt_block(int(bits[i:i + block], 2), key), '016b')
                       for i in range(0, len(bits), block))

    @staticmethod
    def encrypt_ascii(text, key_bits):
        """ASCII 字符串加密：按 2 字节分组，不足补 0x00。"""
        bits = SAESUtils.str_to_bin(text)
        bits += '0' * ((-len(bits)) % BLOCK_SIZE)
        return SAESUtils.encrypt_bits(bits, key_bits)

    @staticmethod
    def decrypt_ascii(cipher_bits, key_bits):
        """ASCII 字符串解密：去除补齐的 0x00 字节。"""
        bits = SAESUtils.decrypt_bits(cipher_bits, key_bits)
        return SAESUtils.bin_to_str(bits).rstrip('\x00')

    # --- 多重加密 ---
    @staticmethod
    def double_encrypt_block(plaintext_16bit, key_32bit):
        """双重加密 C = E_K2(E_K1(P))，密钥高 16 位为 K1、低 16 位为 K2。"""
        k1, k2 = (key_32bit >> 16) & 0xFFFF, key_32bit & 0xFFFF
        return SAESCore.encrypt_block(SAESCore.encrypt_block(plaintext_16bit, k1), k2)

    @staticmethod
    def double_decrypt_block(ciphertext_16bit, key_32bit):
        k1, k2 = (key_32bit >> 16) & 0xFFFF, key_32bit & 0xFFFF
        return SAESCore.decrypt_block(SAESCore.decrypt_block(ciphertext_16bit, k2), k1)

    @staticmethod
    def triple_encrypt_block(plaintext_16bit, key_48bit):
        """三重加密（48-bit 密钥 K1+K2+K3）。"""
        k1, k2, k3 = (key_48bit >> 32) & 0xFFFF, (key_48bit >> 16) & 0xFFFF, key_48bit & 0xFFFF
        return SAESCore.encrypt_block(
            SAESCore.encrypt_block(SAESCore.encrypt_block(plaintext_16bit, k1), k2), k3)

    @staticmethod
    def triple_decrypt_block(ciphertext_16bit, key_48bit):
        k1, k2, k3 = (key_48bit >> 32) & 0xFFFF, (key_48bit >> 16) & 0xFFFF, key_48bit & 0xFFFF
        return SAESCore.decrypt_block(
            SAESCore.decrypt_block(SAESCore.decrypt_block(ciphertext_16bit, k3), k2), k1)

    @staticmethod
    def multi_encrypt_bits(bits, key_int, mode):
        func = SAESUtils.double_encrypt_block if mode == 'double' else SAESUtils.triple_encrypt_block
        return ''.join(format(func(int(bits[i:i + BLOCK_SIZE], 2), key_int), '016b')
                       for i in range(0, len(bits), BLOCK_SIZE))

    @staticmethod
    def multi_decrypt_bits(bits, key_int, mode):
        func = SAESUtils.double_decrypt_block if mode == 'double' else SAESUtils.triple_decrypt_block
        return ''.join(format(func(int(bits[i:i + BLOCK_SIZE], 2), key_int), '016b')
                       for i in range(0, len(bits), BLOCK_SIZE))

    # --- 中间相遇攻击 ---
    @staticmethod
    def meet_in_the_middle(pairs, worker_count=4):
        """中间相遇攻击：枚举 K1 建正向表，枚举 K2 碰撞，多余明密文对过滤伪密钥。

        :param pairs: [(明文 int, 密文 int), ...]
        :return: (候选 [(k1, k2), ...], 耗时秒)
        """
        if not pairs:
            return [], 0.0
        p1, c1 = pairs[0]

        start = time.perf_counter()
        worker_count = max(1, min(int(worker_count), KEY_SPACE))
        chunk = -(-KEY_SPACE // worker_count)
        tasks = [(b, min(b + chunk, KEY_SPACE), p1)
                 for b in range(0, KEY_SPACE, chunk)]

        forward = defaultdict(list)
        if worker_count == 1:
            for table in map(_forward_chunk, tasks):
                for middle, keys in table.items():
                    forward[middle].extend(keys)
        else:
            with ThreadPoolExecutor(max_workers=worker_count) as pool:
                for table in pool.map(_forward_chunk, tasks):
                    for middle, keys in table.items():
                        forward[middle].extend(keys)

        # 反向枚举 K2 并在正向表中碰撞
        candidates = []
        for k2 in range(KEY_SPACE):
            middle = SAESCore.decrypt_block(c1, k2)
            if middle in forward:
                for k1 in forward[middle]:
                    candidates.append((k1, k2))

        # 用额外的明密文对过滤
        for plain, cipher in pairs[1:]:
            candidates = [(k1, k2) for (k1, k2) in candidates
                          if SAESUtils.double_encrypt_block(plain,
                                                            (k1 << 16) | k2) == cipher]
        elapsed = time.perf_counter() - start
        return sorted(candidates), elapsed

    # --- CBC 模式 ---
    @staticmethod
    def generate_iv():
        """随机生成 16-bit 初始向量（IV），需加解密双方共享。"""
        return random.getrandbits(BLOCK_SIZE)

    @staticmethod
    def cbc_encrypt_bits(bits, key_bits, iv_int):
        """CBC 加密：C_i = E(P_i ⊕ C_{i-1})，C_0 = IV。"""
        cipher_blocks = []
        previous = iv_int
        key = int(key_bits, 2)
        for i in range(0, len(bits), BLOCK_SIZE):
            block = int(bits[i:i + BLOCK_SIZE], 2)
            current = SAESCore.encrypt_block(block ^ previous, key)
            cipher_blocks.append(current)
            previous = current
        return ''.join(format(c, '0{}b'.format(BLOCK_SIZE)) for c in cipher_blocks)

    @staticmethod
    def cbc_decrypt_bits(bits, key_bits, iv_int):
        """CBC 解密：P_i = D(C_i) ⊕ C_{i-1}，C_0 = IV。"""
        plain_blocks = []
        previous = iv_int
        key = int(key_bits, 2)
        for i in range(0, len(bits), BLOCK_SIZE):
            current = int(bits[i:i + BLOCK_SIZE], 2)
            block = SAESCore.decrypt_block(current, key) ^ previous
            plain_blocks.append(block)
            previous = current
        return ''.join(format(p, '0{}b'.format(BLOCK_SIZE)) for p in plain_blocks)

    @staticmethod
    def tamper_cipher_block(bits, block_index, bit_position=None):
        """翻转指定密文分组的某一位（缺省随机），返回 (篡改后串, 位下标)。"""
        if bit_position is None:
            bit_position = random.randrange(BLOCK_SIZE)
        blocks = [bits[i:i + BLOCK_SIZE] for i in range(0, len(bits), BLOCK_SIZE)]
        if not 0 <= block_index < len(blocks):
            raise ValueError('分组下标越界')
        block = list(blocks[block_index])
        block[bit_position] = '1' if block[bit_position] == '0' else '0'
        blocks[block_index] = ''.join(block)
        return ''.join(blocks), bit_position


# =================================================================
# 4. GUI 界面模块
# =================================================================
class SAESGUI:
    """四选项卡 Tkinter 界面，对应五个关卡。"""

    def __init__(self, root):
        self.root = root
        self.root.title('S-AES 加解密系统')
        self.root.geometry('820x680')
        self.root.configure(bg='#f0f0f0')

        self.title_font = ('微软雅黑', 16, 'bold')
        self.label_font = ('微软雅黑', 11)
        self.entry_font = ('Consolas', 11)

        tk.Label(root, text='欢迎使用 S-AES 加解密系统',
                 font=self.title_font, bg='#f0f0f0').pack(pady=12)

        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill='both', expand=True, padx=12, pady=6)

        self.tab_basic = tk.Frame(self.notebook, bg='#f0f0f0')
        self.tab_multi = tk.Frame(self.notebook, bg='#f0f0f0')
        self.tab_mitm = tk.Frame(self.notebook, bg='#f0f0f0')
        self.tab_cbc = tk.Frame(self.notebook, bg='#f0f0f0')
        self.notebook.add(self.tab_basic, text='  基础加解密(第1-3关)  ')
        self.notebook.add(self.tab_multi, text='  多重加密(第4关)  ')
        self.notebook.add(self.tab_mitm, text='  中间相遇攻击(第4关)  ')
        self.notebook.add(self.tab_cbc, text='  CBC模式(第5关)  ')

        self._build_basic_tab()
        self._build_multi_tab()
        self._build_mitm_tab()
        self._build_cbc_tab()

    # ---------------- 通用界面辅助 ----------------
    def add_context_menu(self, widget):
        """为输入框绑定右键菜单（复制 / 粘贴 / 全选）。"""
        menu = tk.Menu(widget, tearoff=0)
        menu.add_command(label='复制', command=lambda: widget.event_generate('<<Copy>>'))
        menu.add_command(label='粘贴', command=lambda: widget.event_generate('<<Paste>>'))
        menu.add_separator()
        menu.add_command(label='全选', command=lambda: widget.event_generate('<<SelectAll>>'))
        widget.bind('<Button-3>', lambda e: menu.post(e.x_root, e.y_root))

    def set_placeholder(self, widget, text):
        """设置灰色占位提示文字：获得焦点时清空，失去焦点且为空时恢复。"""
        if isinstance(widget, tk.Text):
            widget.insert('1.0', text)
            widget.config(fg='gray')

            def on_focus_in(_):
                if widget.get('1.0', 'end-1c') == text:
                    widget.delete('1.0', 'end')
                    widget.config(fg='black')

            def on_focus_out(_):
                if widget.get('1.0', 'end-1c') == '':
                    widget.insert('1.0', text)
                    widget.config(fg='gray')
        else:
            widget.insert(0, text)
            widget.config(fg='gray')

            def on_focus_in(_):
                if widget.get() == text:
                    widget.delete(0, 'end')
                    widget.config(fg='black')

            def on_focus_out(_):
                if widget.get() == '':
                    widget.insert(0, text)
                    widget.config(fg='gray')

        widget.bind('<FocusIn>', on_focus_in)
        widget.bind('<FocusOut>', on_focus_out)

    @staticmethod
    def now():
        """当前系统时间字符串，用于给测试结果打时间戳。"""
        return datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')

    @staticmethod
    def compact(text):
        """去除输入中的所有空白字符，方便用户分组书写二进制串。"""
        return ''.join(text.split())

    # =================================================================
    # 选项卡 1：基础加解密（第 1 关 / 第 2 关 / 第 3 关）
    # =================================================================
    def _build_basic_tab(self):
        tab = self.tab_basic
        tk.Label(tab, text='第1关：16 bit 数据 + 16 bit 密钥；第3关：ASCII 字符串（自动按 2 字节分组）',
                 font=('微软雅黑', 9, 'italic'), bg='#f0f0f0', fg='gray').pack(pady=6)

        form = tk.Frame(tab, bg='#f0f0f0')
        form.pack(pady=4)

        tk.Label(form, text='明文：', font=self.label_font, bg='#f0f0f0').grid(
            row=0, column=0, padx=8, pady=5, sticky='ne')
        self.basic_plain = tk.Text(form, font=self.entry_font, width=60, height=3, wrap='word')
        self.basic_plain.grid(row=0, column=1, padx=8, pady=5)
        self.add_context_menu(self.basic_plain)
        self.set_placeholder(self.basic_plain, '请输入16位二进制串，或任意长度的ASCII字符串')

        tk.Label(form, text='密钥：', font=self.label_font, bg='#f0f0f0').grid(
            row=1, column=0, padx=8, pady=5, sticky='e')
        self.basic_key = tk.Entry(form, font=self.entry_font, width=60)
        self.basic_key.grid(row=1, column=1, padx=8, pady=5, ipady=3)
        self.add_context_menu(self.basic_key)
        self.set_placeholder(self.basic_key, '请输入16位二进制密钥')

        tk.Label(form, text='密文：', font=self.label_font, bg='#f0f0f0').grid(
            row=2, column=0, padx=8, pady=5, sticky='ne')
        self.basic_cipher = tk.Text(form, font=self.entry_font, width=60, height=3, wrap='word')
        self.basic_cipher.grid(row=2, column=1, padx=8, pady=5)
        self.add_context_menu(self.basic_cipher)

        actions = tk.Frame(tab, bg='#f0f0f0')
        actions.pack(pady=12)
        # 状态栏独占一行并允许自动换行，避免长文本被固定宽度截断
        self.basic_status = tk.Label(actions, text='', font=('微软雅黑', 10),
                                     fg='blue', bg='#f0f0f0', wraplength=700,
                                     justify='center')
        self.basic_status.pack(pady=(0, 8))
        btn_row = tk.Frame(actions, bg='#f0f0f0')
        btn_row.pack()
        tk.Button(btn_row, text='点击加密', width=12, font=('微软雅黑', 11),
                  command=self.basic_encrypt).pack(side='left', padx=8)
        tk.Button(btn_row, text='点击解密', width=12, font=('微软雅黑', 11),
                  command=self.basic_decrypt).pack(side='left', padx=8)

        tk.Label(tab, text='说明：二进制输入允许用空格分组（如 “10101010 10101010”）；'
                          'ASCII 字符串长度为奇数时自动补 0x00 字节。',
                 font=('微软雅黑', 9), bg='#f0f0f0', fg='gray', wraplength=720,
                 justify='left').pack(side='bottom', pady=8)

    def _read_basic_key(self):
        """校验并读取 16 位二进制密钥。"""
        key = self.compact(self.basic_key.get())
        if len(key) != 16 or not all(c in '01' for c in key):
            messagebox.showerror('错误', '密钥必须是 16 位二进制串！')
            return None
        return key

    @staticmethod
    def _read_text(widget, placeholder=None):
        text = widget.get('1.0', 'end-1c').strip()
        if placeholder and text == placeholder:
            return ''
        return text

    def basic_encrypt(self):
        key = self._read_basic_key()
        if key is None:
            return
        raw = self._read_text(self.basic_plain,
                              '请输入16位二进制串，或任意长度的ASCII字符串')
        if not raw:
            messagebox.showwarning('提示', '请输入要加密的内容！')
            return
        compact = self.compact(raw)
        try:
            if compact and all(c in '01' for c in compact):
                # 二进制模式：长度必须是 16 的倍数
                if len(compact) % BLOCK_SIZE != 0:
                    messagebox.showwarning('提示', '二进制串长度必须是 16 的倍数（16、32、48……）！')
                    return
                cipher = SAESUtils.encrypt_bits(compact, key)
                note = '加密完成（二进制 %d 位）' % len(cipher)
            else:
                # ASCII 模式：按 2 字节分组
                cipher = SAESUtils.encrypt_ascii(raw, key)
                note = '加密完成（ASCII 共 %d 个字符，密文 %d 位）' % (len(raw), len(cipher))
            self.basic_cipher.delete('1.0', 'end')
            self.basic_cipher.insert('1.0', cipher)
            self.basic_status.config(text=note, fg='green')
        except Exception as exc:
            messagebox.showerror('错误', str(exc))

    def basic_decrypt(self):
        key = self._read_basic_key()
        if key is None:
            return
        cipher_raw = self.compact(self._read_text(self.basic_cipher))
        if not cipher_raw:
            messagebox.showwarning('提示', '请先在密文框中输入密文！')
            return
        if len(cipher_raw) % BLOCK_SIZE != 0 or not all(c in '01' for c in cipher_raw):
            messagebox.showerror('错误', '密文必须是长度为 16 倍数的二进制串！')
            return

        # 只解密一次，再由二进制结果派生 ASCII，避免重复计算
        plain_bits = SAESUtils.decrypt_bits(cipher_raw, key)
        ascii_text = SAESUtils.bin_to_str(plain_bits).rstrip('\x00')
        self.basic_plain.delete('1.0', 'end')
        if SAESUtils.is_printable(ascii_text):
            # 原始输入为 ASCII 文本（第 3 关），明文框直接还原可读文本
            self.basic_plain.insert('1.0', ascii_text)
            self.basic_status.config(
                text='解密完成（ASCII：%s；二进制：%s）' % (ascii_text, plain_bits),
                fg='blue')
        else:
            self.basic_plain.insert('1.0', plain_bits)
            self.basic_status.config(
                text='解密完成（二进制：%s；ASCII：%s）'
                     % (plain_bits, ascii_text if ascii_text else '(不可打印)'),
                fg='blue')
        self.basic_plain.config(fg='black')

    # =================================================================
    # 选项卡 2：双重 / 三重加密（第 4 关 4.1 / 4.3）
    # =================================================================
    def _build_multi_tab(self):
        tab = self.tab_multi
        top = tk.Frame(tab, bg='#f0f0f0')
        top.pack(pady=8)
        tk.Label(top, text='加密模式：', font=self.label_font, bg='#f0f0f0').pack(side='left')
        self.multi_mode = tk.StringVar(value='double')
        tk.Radiobutton(top, text='双重加密（32 bit 密钥 K1+K2）', variable=self.multi_mode,
                       value='double', bg='#f0f0f0', font=self.label_font,
                       command=self._update_key_hint).pack(side='left', padx=8)
        tk.Radiobutton(top, text='三重加密（48 bit 密钥 K1+K2+K3）', variable=self.multi_mode,
                       value='triple', bg='#f0f0f0', font=self.label_font,
                       command=self._update_key_hint).pack(side='left', padx=8)

        form = tk.Frame(tab, bg='#f0f0f0')
        form.pack(pady=4)
        tk.Label(form, text='明文：', font=self.label_font, bg='#f0f0f0').grid(
            row=0, column=0, padx=8, pady=5, sticky='ne')
        self.multi_plain = tk.Text(form, font=self.entry_font, width=60, height=3, wrap='word')
        self.multi_plain.grid(row=0, column=1, padx=8, pady=5)
        self.add_context_menu(self.multi_plain)
        self.set_placeholder(self.multi_plain, '请输入 16 位整数倍的二进制串，或 ASCII 字符串')

        tk.Label(form, text='密钥：', font=self.label_font, bg='#f0f0f0').grid(
            row=1, column=0, padx=8, pady=5, sticky='e')
        self.multi_key = tk.Entry(form, font=self.entry_font, width=60)
        self.multi_key.grid(row=1, column=1, padx=8, pady=5, ipady=3)
        self.add_context_menu(self.multi_key)
        self.multi_key_hint = tk.StringVar(value='请输入 32 位二进制密钥（K1 的 16 位 + K2 的 16 位）')
        self.set_placeholder(self.multi_key, self.multi_key_hint.get())

        tk.Label(form, text='密文：', font=self.label_font, bg='#f0f0f0').grid(
            row=2, column=0, padx=8, pady=5, sticky='ne')
        self.multi_cipher = tk.Text(form, font=self.entry_font, width=60, height=3, wrap='word')
        self.multi_cipher.grid(row=2, column=1, padx=8, pady=5)
        self.add_context_menu(self.multi_cipher)

        actions = tk.Frame(tab, bg='#f0f0f0')
        actions.pack(pady=12)
        self.multi_status = tk.Label(actions, text='', font=('微软雅黑', 10),
                                     fg='blue', bg='#f0f0f0', width=20)
        self.multi_status.grid(row=0, column=0, padx=10)
        tk.Button(actions, text='点击加密', width=12, font=('微软雅黑', 11),
                  command=self.multi_encrypt).grid(row=0, column=1, padx=8)
        tk.Button(actions, text='点击解密', width=12, font=('微软雅黑', 11),
                  command=self.multi_decrypt).grid(row=0, column=2, padx=8)

    def _update_key_hint(self):
        """切换双重 / 三重模式时更新密钥框提示。"""
        if self.multi_mode.get() == 'double':
            hint = '请输入 32 位二进制密钥（K1 的 16 位 + K2 的 16 位）'
        else:
            hint = '请输入 48 位二进制密钥（K1、K2、K3 各 16 位顺序拼接）'
        if self.multi_key.get() in ('', self.multi_key_hint.get()):
            self.multi_key.delete(0, 'end')
            self.multi_key.insert(0, hint)
            self.multi_key.config(fg='gray')
        self.multi_key_hint.set(hint)

    def _read_multi_key(self):
        """按当前模式校验密钥，返回整数密钥或 None。"""
        mode = self.multi_mode.get()
        need = 32 if mode == 'double' else 48
        key = self.compact(self.multi_key.get())
        if key == self.multi_key_hint.get():
            key = ''
        if len(key) != need or not all(c in '01' for c in key):
            messagebox.showerror('错误', '%s要求输入 %d 位二进制密钥！'
                                 % ('双重加密' if need == 32 else '三重加密', need))
            return None
        return int(key, 2)

    def _multi_input_bits(self, raw):
        """把多重加密的明文输入转换为二进制，返回 (bits, 是否ASCII)。"""
        compact = self.compact(raw)
        if compact and all(c in '01' for c in compact):
            if len(compact) % BLOCK_SIZE != 0:
                raise ValueError('二进制串长度必须是 16 的倍数！')
            return compact, False
        bits = SAESUtils.str_to_bin(raw)
        bits += '0' * ((-len(bits)) % BLOCK_SIZE)
        return bits, True

    def multi_encrypt(self):
        key_int = self._read_multi_key()
        if key_int is None:
            return
        raw = self._read_text(self.multi_plain,
                              '请输入 16 位整数倍的二进制串，或 ASCII 字符串')
        if not raw:
            messagebox.showwarning('提示', '请输入要加密的内容！')
            return
        try:
            bits, _ = self._multi_input_bits(raw)
            cipher = SAESUtils.multi_encrypt_bits(bits, key_int, self.multi_mode.get())
            self.multi_cipher.delete('1.0', 'end')
            self.multi_cipher.insert('1.0', cipher)
            self.multi_status.config(text='加密完成', fg='green')
        except Exception as exc:
            messagebox.showerror('错误', str(exc))

    def multi_decrypt(self):
        key_int = self._read_multi_key()
        if key_int is None:
            return
        cipher = self.compact(self._read_text(self.multi_cipher))
        if len(cipher) % BLOCK_SIZE != 0 or not all(c in '01' for c in cipher):
            messagebox.showerror('错误', '密文必须是长度为 16 倍数的二进制串！')
            return
        bits = SAESUtils.multi_decrypt_bits(cipher, key_int, self.multi_mode.get())
        ascii_text = SAESUtils.bin_to_str(bits).rstrip('\x00')
        self.multi_plain.delete('1.0', 'end')
        if SAESUtils.is_printable(ascii_text):
            self.multi_plain.insert('1.0', ascii_text)
            self.multi_status.config(text='解密完成（ASCII）', fg='blue')
        else:
            self.multi_plain.insert('1.0', bits)
            self.multi_status.config(text='解密完成（二进制）', fg='blue')
        self.multi_plain.config(fg='black')

    # =================================================================
    # 选项卡 3：中间相遇攻击（第 4 关 4.2）
    # =================================================================
    def _build_mitm_tab(self):
        tab = self.tab_mitm
        tk.Label(tab, text='给定一个或多个使用相同密钥（K1+K2）的明密文对，'
                          '用中间相遇攻击恢复 32 bit 双重加密密钥。',
                 font=('微软雅黑', 10), bg='#f0f0f0', wraplength=740,
                 justify='left').pack(pady=6)

        form = tk.Frame(tab, bg='#f0f0f0')
        form.pack(pady=4)
        tk.Label(form, text='明文 P：', font=self.label_font, bg='#f0f0f0').grid(
            row=0, column=0, padx=8, pady=5, sticky='e')
        self.mitm_plain = tk.Entry(form, font=self.entry_font, width=50)
        self.mitm_plain.grid(row=0, column=1, padx=8, pady=5, ipady=3)
        self.add_context_menu(self.mitm_plain)
        self.set_placeholder(self.mitm_plain, '16 位二进制明文，例如 0000000000000000')

        tk.Label(form, text='密文 C：', font=self.label_font, bg='#f0f0f0').grid(
            row=1, column=0, padx=8, pady=5, sticky='e')
        self.mitm_cipher = tk.Entry(form, font=self.entry_font, width=50)
        self.mitm_cipher.grid(row=1, column=1, padx=8, pady=5, ipady=3)
        self.add_context_menu(self.mitm_cipher)
        self.set_placeholder(self.mitm_cipher, '16 位二进制密文')

        tk.Label(form, text='追加明密文对：', font=self.label_font, bg='#f0f0f0').grid(
            row=2, column=0, padx=8, pady=5, sticky='e')
        self.mitm_extra = tk.Entry(form, font=self.entry_font, width=50)
        self.mitm_extra.grid(row=2, column=1, padx=8, pady=5, ipady=3)
        self.add_context_menu(self.mitm_extra)
        self.set_placeholder(self.mitm_extra, '可选，形如 P1,C1;P2,C2（用于进一步过滤候选密钥）')

        actions = tk.Frame(tab, bg='#f0f0f0')
        actions.pack(pady=8)
        tk.Label(actions, text='线程数：', font=self.label_font, bg='#f0f0f0').grid(
            row=0, column=0)
        self.mitm_workers = tk.Spinbox(actions, from_=1, to=16, width=5,
                                       font=self.label_font)
        self.mitm_workers.grid(row=0, column=1, padx=6)
        self.mitm_workers.delete(0, 'end')
        self.mitm_workers.insert(0, str(min(8, (os.cpu_count() or 4))))
        self.mitm_btn = tk.Button(actions, text='开始中间相遇攻击', width=18,
                                  font=('微软雅黑', 11), command=self.mitm_run)
        self.mitm_btn.grid(row=0, column=2, padx=12)

        tk.Label(tab, text='攻击结果：', font=self.label_font, bg='#f0f0f0').pack(
            anchor='w', padx=30)
        self.mitm_result = tk.Text(tab, font=self.entry_font, width=88, height=16,
                                   wrap='word')
        self.mitm_result.pack(padx=20, pady=4)
        self.add_context_menu(self.mitm_result)

    @staticmethod
    def _parse_16bits(entry, placeholder):
        value = entry.get().strip()
        if value == placeholder:
            value = ''
        value = SAESGUI.compact(value)
        if len(value) != 16 or not all(c in '01' for c in value):
            return None
        return value

    def mitm_run(self):
        """中间相遇攻击（后台线程执行，避免 GUI 假死）。"""
        p = self._parse_16bits(self.mitm_plain, '16 位二进制明文，例如 0000000000000000')
        c = self._parse_16bits(self.mitm_cipher, '16 位二进制密文')
        if p is None or c is None:
            messagebox.showerror('错误', '请输入合法的 16 位二进制明文与密文！')
            return
        pairs = [(int(p, 2), int(c, 2))]

        extra = self.mitm_extra.get().strip()
        if extra and extra != '可选，形如 P1,C1;P2,C2（用于进一步过滤候选密钥）':
            try:
                for item in extra.split(';'):
                    item = item.strip()
                    if not item:
                        continue
                    px, cx = item.split(',')
                    px, cx = self.compact(px), self.compact(cx)
                    if len(px) != 16 or len(cx) != 16:
                        raise ValueError
                    pairs.append((int(px, 2), int(cx, 2)))
            except ValueError:
                messagebox.showerror('错误', '追加明密文对格式错误！')
                return

        workers = int(self.mitm_workers.get())
        self.mitm_result.delete('1.0', 'end')
        self.mitm_result.insert('1.0', '正在枚举 2×65536 个密钥，请稍候……'
                                      '(界面不会卡死，请勿多次点击)\n')
        self.mitm_btn.config(state='disabled')  # 计算期间禁用按钮
        start_at = self.now()
        pair_count = len(pairs)

        def _run_in_background():
            candidates, elapsed = SAESUtils.meet_in_the_middle(pairs, workers)
            end_at = self.now()
            # Tk 控件只能在主线程操作，用 root.after 回传结果
            self.root.after(0, lambda: self._update_mitm_ui(
                candidates, elapsed, workers, start_at, end_at, pair_count))

        threading.Thread(target=_run_in_background, daemon=True).start()

    def _update_mitm_ui(self, candidates, elapsed, workers, start_at, end_at, pair_count):
        """中间相遇攻击完成后，在主线程更新结果区与按钮状态。"""
        self.mitm_btn.config(state='normal')
        report = '【中间相遇攻击结果】\n'
        report += '明密文对数量：%d\n' % pair_count
        report += '开始时间：%s\n' % start_at
        report += '结束时间：%s\n' % end_at
        report += '耗时：%.4f 秒（%d 线程）\n\n' % (elapsed, workers)
        if candidates:
            report += '共找到 %d 个满足条件的密钥 (K1, K2)：\n' % len(candidates)
            for k1, k2 in candidates[:200]:
                report += '  K1 = %s，K2 = %s（32 bit 密钥：%s%s）\n' % (
                    format(k1, '016b'), format(k2, '016b'),
                    format(k1, '016b'), format(k2, '016b'))
            if len(candidates) > 200:
                report += '  ……（仅显示前 200 个，共 %d 个）\n' % len(candidates)
            report += '\n说明：单个明密文对通常无法唯一确定密钥（多重加密的密钥碰撞），'
            report += '追加更多明密文对可把候选收敛到唯一解。\n'
        else:
            report += '未找到满足条件的密钥对，请检查明密文输入。\n'
        self.mitm_result.delete('1.0', 'end')
        self.mitm_result.insert('1.0', report)

    # =================================================================
    # 选项卡 4：CBC 模式（第 5 关）
    # =================================================================
    def _build_cbc_tab(self):
        tab = self.tab_cbc
        form = tk.Frame(tab, bg='#f0f0f0')
        form.pack(pady=6)

        tk.Label(form, text='密钥：', font=self.label_font, bg='#f0f0f0').grid(
            row=0, column=0, padx=8, pady=4, sticky='e')
        self.cbc_key = tk.Entry(form, font=self.entry_font, width=48)
        self.cbc_key.grid(row=0, column=1, padx=8, pady=4, ipady=3)
        self.add_context_menu(self.cbc_key)
        self.set_placeholder(self.cbc_key, '16 位二进制密钥')

        iv_row = tk.Frame(form, bg='#f0f0f0')
        iv_row.grid(row=1, column=1, sticky='w', padx=8, pady=2)
        tk.Label(form, text='初始向量 IV：', font=self.label_font, bg='#f0f0f0').grid(
            row=1, column=0, padx=8, pady=4, sticky='e')
        self.cbc_iv = tk.Entry(iv_row, font=self.entry_font, width=28)
        self.cbc_iv.pack(side='left')
        self.add_context_menu(self.cbc_iv)
        self.set_placeholder(self.cbc_iv, '16 位二进制 IV')
        tk.Button(iv_row, text='随机生成 IV', font=('微软雅黑', 9),
                  command=self.cbc_gen_iv).pack(side='left', padx=8)

        tk.Label(form, text='明文：', font=self.label_font, bg='#f0f0f0').grid(
            row=2, column=0, padx=8, pady=4, sticky='ne')
        self.cbc_plain = tk.Text(form, font=self.entry_font, width=48, height=3, wrap='word')
        self.cbc_plain.grid(row=2, column=1, padx=8, pady=4)
        self.add_context_menu(self.cbc_plain)
        self.set_placeholder(self.cbc_plain, '16 位整数倍的二进制串，或 ASCII 字符串')

        tk.Label(form, text='密文：', font=self.label_font, bg='#f0f0f0').grid(
            row=3, column=0, padx=8, pady=4, sticky='ne')
        self.cbc_cipher = tk.Text(form, font=self.entry_font, width=48, height=3, wrap='word')
        self.cbc_cipher.grid(row=3, column=1, padx=8, pady=4)
        self.add_context_menu(self.cbc_cipher)

        actions = tk.Frame(tab, bg='#f0f0f0')
        actions.pack(pady=8)
        tk.Button(actions, text='CBC 加密', width=12, font=('微软雅黑', 11),
                  command=self.cbc_encrypt).grid(row=0, column=0, padx=8)
        tk.Button(actions, text='CBC 解密', width=12, font=('微软雅黑', 11),
                  command=self.cbc_decrypt).grid(row=0, column=1, padx=8)
        tk.Button(actions, text='篡改第 2 个密文分组后解密', width=24, font=('微软雅黑', 10),
                  command=self.cbc_tamper).grid(row=0, column=2, padx=8)

        self.cbc_status = tk.Label(tab, text='', font=('微软雅黑', 10), fg='blue',
                                   bg='#f0f0f0', wraplength=740, justify='left')
        self.cbc_status.pack(pady=4)

    def cbc_gen_iv(self):
        iv = format(SAESUtils.generate_iv(), '016b')
        self.cbc_iv.delete(0, 'end')
        self.cbc_iv.insert(0, iv)
        self.cbc_iv.config(fg='black')

    def _read_cbc_key_iv(self):
        key = self.compact(self.cbc_key.get())
        iv = self.compact(self.cbc_iv.get())
        if len(key) != 16 or not all(c in '01' for c in key):
            messagebox.showerror('错误', '请输入 16 位二进制密钥！')
            return None
        if len(iv) != 16 or not all(c in '01' for c in iv):
            messagebox.showerror('错误', '请输入 16 位二进制初始向量 IV（可随机生成）！')
            return None
        return key, int(iv, 2)

    @staticmethod
    def _cbc_to_bits(raw):
        compact = SAESGUI.compact(raw)
        if compact and all(c in '01' for c in compact):
            if len(compact) % BLOCK_SIZE != 0:
                raise ValueError('二进制串长度必须是 16 的倍数！')
            return compact
        bits = SAESUtils.str_to_bin(raw)
        bits += '0' * ((-len(bits)) % BLOCK_SIZE)
        return bits

    def cbc_encrypt(self):
        checked = self._read_cbc_key_iv()
        if checked is None:
            return
        key, iv = checked
        raw = self._read_text(self.cbc_plain, '16 位整数倍的二进制串，或 ASCII 字符串')
        if not raw:
            messagebox.showwarning('提示', '请输入明文！')
            return
        try:
            bits = self._cbc_to_bits(raw)
            cipher = SAESUtils.cbc_encrypt_bits(bits, key, iv)
            self.cbc_cipher.delete('1.0', 'end')
            self.cbc_cipher.insert('1.0', cipher)
            self.cbc_status.config(text='CBC 加密完成，共 %d 个密文分组（相同明文分组在 CBC 下密文不同）。'
                                        % (len(cipher) // BLOCK_SIZE))
        except Exception as exc:
            messagebox.showerror('错误', str(exc))

    def cbc_decrypt(self, show_status=True):
        checked = self._read_cbc_key_iv()
        if checked is None:
            return None
        key, iv = checked
        cipher = self.compact(self._read_text(self.cbc_cipher))
        if len(cipher) % BLOCK_SIZE != 0 or not all(c in '01' for c in cipher):
            messagebox.showerror('错误', '密文必须是长度为 16 倍数的二进制串！')
            return None
        bits = SAESUtils.cbc_decrypt_bits(cipher, key, iv)
        text = SAESUtils.bin_to_str(bits).rstrip('\x00')
        self.cbc_plain.delete('1.0', 'end')
        if SAESUtils.is_printable(text):
            self.cbc_plain.insert('1.0', text)
        else:
            self.cbc_plain.insert('1.0', bits)
        self.cbc_plain.config(fg='black')
        if show_status:
            self.cbc_status.config(text='CBC 解密完成。')
        return bits

    def cbc_tamper(self):
        """翻转第 2 个密文分组的某一位后解密，弹窗对比篡改前后的明文。"""
        checked = self._read_cbc_key_iv()
        if checked is None:
            return
        key, iv = checked
        original_cipher = self.compact(self._read_text(self.cbc_cipher))
        if len(original_cipher) < 2 * BLOCK_SIZE:
            messagebox.showwarning('提示', '密文至少要有 2 个分组才能演示篡改效果，请先加密较长明文！')
            return
        original_plain = SAESUtils.cbc_decrypt_bits(original_cipher, key, iv)
        tampered, bit_pos = SAESUtils.tamper_cipher_block(original_cipher, block_index=1)
        tampered_plain = SAESUtils.cbc_decrypt_bits(tampered, key, iv)
        flipped = BLOCK_SIZE - bit_pos

        self.cbc_cipher.delete('1.0', 'end')
        self.cbc_cipher.insert('1.0', tampered)
        self.cbc_plain.delete('1.0', 'end')
        self.cbc_plain.insert('1.0', tampered_plain)
        self.cbc_plain.config(fg='black')
        self.cbc_status.config(
            text='已翻转第 2 个密文分组的第 %d 位（从高位起计）。\n'
                 'P2 因雪崩完全错乱，P3 仅同一位翻转，P1/P4 不变。' % flipped)

        msg = '【CBC 密文篡改 · 错误传播对比】\n\n'
        msg += '翻转位置：第 2 个密文分组的第 %d 位（从高位起计）\n\n' % flipped
        msg += '解密后明文（篡改前）：\n%s\n\n' % original_plain
        msg += '解密后明文（篡改后）：\n%s\n\n' % tampered_plain
        msg += '规律说明：\n'
        msg += '1. 第 1 个分组不受影响；\n'
        msg += '2. 第 2 个分组因雪崩效应完全乱码；\n'
        msg += '3. 第 3 个分组仅对应位翻转（P3 = D(C3) ⊕ C2）；\n'
        msg += '4. 第 4 个及之后的分组不受影响。'
        messagebox.showinfo('CBC 篡改对比', msg)


if __name__ == '__main__':
    root = tk.Tk()
    SAESGUI(root)
    root.mainloop()
