# -*- coding: utf-8 -*-
"""
S-DES（Simplified DES）加解密系统
================================================================
《信息安全导论》课程作业 · S-DES 算法实现

关卡覆盖：
    第 1 关  基础加解密：8-bit 明文 + 10-bit 密钥 -> 8-bit 密文
    第 2 关  交叉测试：算法流程与转换单位均遵循课程给定标准，可与其他小组程序互相对比
    第 3 关  ASCII 扩展：按 1 Byte 分组，支持任意长度字符串的加解密
    第 4 关  暴力破解：给定明密文对遍历 1024 个密钥，支持多进程 / 多线程 / 串行三种模式并打时间戳
    第 5 关  封闭测试：分析是否存在多个密钥 K 使得 E(K, P) = C，即密钥碰撞现象

模块划分：
    SDESCore   核心算法：置换、循环左移、S 盒查表、密钥扩展、轮函数 F、加解密主流程
    SDESUtils  工具函数：编码转换、暴力破解、并行性能对比、密钥碰撞分析
    SDESGUI    图形界面：输入校验、事件响应、右键菜单、结果弹窗

运行方式（在项目根目录下执行）：
    python src/sdes.py
"""

import datetime
import os
import time
import tkinter as tk
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from tkinter import messagebox

# =================================================================
# 1. 算法常量
#    以下置换表中的数字均表示“取输入比特串的第 i 位”，下标从 1 开始计数
# =================================================================
P10 = (3, 5, 2, 7, 4, 10, 1, 9, 8, 6)      # 密钥置换：10 bit -> 10 bit
P8 = (6, 3, 7, 4, 8, 5, 10, 9)             # 压缩置换：10 bit -> 8 bit，用于生成子密钥
IP = (2, 6, 3, 1, 4, 8, 5, 7)              # 初始置换 IP
IP_INV = (4, 1, 3, 5, 7, 2, 8, 6)          # 初始置换的逆 IP^-1
EP = (4, 1, 2, 3, 2, 3, 4, 1)              # 轮函数中的扩展置换：4 bit -> 8 bit
SP = (2, 4, 3, 1)                          # S 盒输出后的置换：4 bit -> 4 bit
SHIFT1 = (2, 3, 4, 5, 1)                   # 左移 1 位的等价置换表
SHIFT2 = (3, 4, 5, 1, 2)                   # 左移 2 位的等价置换表（在第一次移位结果上再移 2 位）

# S 盒：行号由 4 位输入的第 1、4 位组成，列号由第 2、3 位组成，输出 2 bit
SBOX1 = [[1, 0, 3, 2], [3, 2, 1, 0], [0, 2, 1, 3], [3, 1, 0, 2]]
SBOX2 = [[0, 1, 2, 3], [2, 3, 1, 0], [3, 0, 1, 2], [2, 1, 0, 3]]

KEY_SPACE = 1024                            # 10 bit 密钥的取值空间大小：2^10


# =================================================================
# 2. 核心算法模块
# =================================================================
class SDESCore:
    """S-DES 核心算法：所有方法均为纯函数（输入决定输出，无副作用），便于测试与复用。"""

    @staticmethod
    def permute(bits, table):
        """通用置换：按 table 指定的顺序重新排列比特串。

        :param bits:  输入比特串，如 '10101010'
        :param table: 置换表，元素为 1 开始的下标
        :return:      置换后的比特串
        """
        return ''.join(bits[i - 1] for i in table)

    @staticmethod
    def left_shift(bits, shift_table):
        """循环左移：用置换表实现 5 bit 半密钥的循环左移（SHIFT1 移 1 位，SHIFT2 移 2 位）。"""
        return ''.join(bits[i - 1] for i in shift_table)

    @staticmethod
    def xor(bits_a, bits_b):
        """按位异或：逐位比较，相同为 '0'，不同为 '1'。"""
        return ''.join('0' if a == b else '1' for a, b in zip(bits_a, bits_b))

    @staticmethod
    def sbox_lookup(bits, sbox):
        """S 盒查表：4 bit 输入 -> 2 bit 输出。

        行号 = 第 1 位与第 4 位组成的二进制数
        列号 = 第 2 位与第 3 位组成的二进制数
        """
        row = int(bits[0] + bits[3], 2)
        col = int(bits[1] + bits[2], 2)
        return format(sbox[row][col], '02b')

    @staticmethod
    def generate_keys(key_10bit):
        """密钥扩展：由 10 bit 主密钥生成两个 8 bit 子密钥 K1、K2。

        流程：P10 置换 -> 拆分为左右各 5 bit -> 分别循环左移 1 位 -> P8 压缩得 K1
              -> 在第一次移位结果上再循环左移 2 位（累计左移 2 位） -> P8 压缩得 K2
        """
        key_p10 = SDESCore.permute(key_10bit, P10)
        left, right = key_p10[:5], key_p10[5:]
        ls1_left = SDESCore.left_shift(left, SHIFT1)
        ls1_right = SDESCore.left_shift(right, SHIFT1)
        k1 = SDESCore.permute(ls1_left + ls1_right, P8)
        ls2_left = SDESCore.left_shift(ls1_left, SHIFT2)
        ls2_right = SDESCore.left_shift(ls1_right, SHIFT2)
        k2 = SDESCore.permute(ls2_left + ls2_right, P8)
        return k1, k2

    @staticmethod
    def f_function(right_4bits, subkey_8bit):
        """轮函数 F：4 bit 右半分组 + 8 bit 子密钥 -> 4 bit 输出。

        流程：EP 扩展为 8 bit -> 与子密钥异或 -> 左右各 4 bit 分别过 S1、S2 -> SP 置换。
        """
        expanded = SDESCore.permute(right_4bits, EP)
        xor_result = SDESCore.xor(expanded, subkey_8bit)
        left_sbox = SDESCore.sbox_lookup(xor_result[:4], SBOX1)
        right_sbox = SDESCore.sbox_lookup(xor_result[4:], SBOX2)
        return SDESCore.permute(left_sbox + right_sbox, SP)

    @staticmethod
    def encrypt(plaintext_8bit, key_10bit):
        """S-DES 加密：IP -> fK1 -> SW（左右互换）-> fK2 -> IP^-1。"""
        k1, k2 = SDESCore.generate_keys(key_10bit)
        ip = SDESCore.permute(plaintext_8bit, IP)
        left, right = ip[:4], ip[4:]

        # 第一轮：左半与 F(右半, K1) 异或
        f1 = SDESCore.f_function(right, k1)
        xor1 = SDESCore.xor(left, f1)

        # SW：交换左右两半，第二轮的输入为 (右半, 第一轮异或结果)
        sw_left, sw_right = right, xor1
        f2 = SDESCore.f_function(sw_right, k2)
        xor2 = SDESCore.xor(sw_left, f2)

        # 注意：不再交换回来，直接拼接后做 IP 逆置换
        return SDESCore.permute(xor2 + sw_right, IP_INV)

    @staticmethod
    def decrypt(ciphertext_8bit, key_10bit):
        """S-DES 解密：结构与加密完全相同，只是子密钥使用顺序相反（先 K2 后 K1）。"""
        k1, k2 = SDESCore.generate_keys(key_10bit)
        ip = SDESCore.permute(ciphertext_8bit, IP)
        left, right = ip[:4], ip[4:]

        f1 = SDESCore.f_function(right, k2)
        xor1 = SDESCore.xor(left, f1)

        sw_left, sw_right = right, xor1
        f2 = SDESCore.f_function(sw_right, k1)
        xor2 = SDESCore.xor(sw_left, f2)

        return SDESCore.permute(xor2 + sw_right, IP_INV)


# =================================================================
# 3. 扩展与测试工具模块
# =================================================================
def _scan_key_range(task):
    """扫描一段密钥区间，返回所有能把明文加密成目标密文的密钥。

    定义为模块级函数（而非类内方法）是因为：Windows 下的多进程采用 spawn 模式，
    子进程需要能够 pickle 导入该函数，类内方法或 lambda 无法被正确序列化。

    :param task: 元组 (begin, end, plaintext, ciphertext, repeat)
                 repeat 表示对每个候选密钥重复验证的次数，仅用于性能对照实验
    :return:     命中的 10 bit 密钥列表
    """
    begin, end, plaintext, ciphertext, repeat = task
    hits = []
    for key_int in range(begin, end):
        key = format(key_int, '010b')
        matched = True
        for _ in range(repeat):
            # 命中与否都完成 repeat 次验证，保证每个候选密钥的计算代价一致
            if SDESCore.encrypt(plaintext, key) != ciphertext:
                matched = False
        if matched:
            hits.append(key)
    return hits


class SDESUtils:
    """工具函数集合：编码转换、暴力破解、并行性能对比、密钥碰撞分析。"""

    @staticmethod
    def str_to_bin(text):
        """ASCII 字符串 -> 二进制串（每个字符 1 Byte = 8 bit）。"""
        return ''.join(format(ord(c), '08b') for c in text)

    @staticmethod
    def bin_to_str(bits):
        """二进制串 -> ASCII 字符串，按 8 bit 一组转换，末尾不足 8 bit 的部分丢弃。"""
        chars = []
        for i in range(0, len(bits), 8):
            byte = bits[i:i + 8]
            if len(byte) == 8:
                chars.append(chr(int(byte, 2)))
        return ''.join(chars)

    @staticmethod
    def is_printable(text):
        """判断字符串是否全部由可打印 ASCII 字符组成（用于决定解密结果以文本还是二进制展示）。"""
        return bool(text) and all(32 <= ord(ch) < 127 for ch in text)

    @staticmethod
    def _build_tasks(plaintext_8bit, ciphertext_8bit, worker_count, repeat):
        """把 1024 个密钥切成若干连续区间，交给不同的进程 / 线程并行处理。

        按“块”而不是按“单个密钥”分发任务，可以大幅减少任务调度与进程间通信的开销。
        """
        worker_count = max(1, min(int(worker_count), KEY_SPACE))
        chunk_size = -(-KEY_SPACE // worker_count)          # 向上取整
        tasks = []
        for begin in range(0, KEY_SPACE, chunk_size):
            end = min(begin + chunk_size, KEY_SPACE)
            tasks.append((begin, end, plaintext_8bit, ciphertext_8bit, repeat))
        return tasks

    @staticmethod
    def brute_force(plaintext_8bit, ciphertext_8bit, worker_count=None,
                    mode='process', repeat=1):
        """遍历 1024 个密钥，找出所有满足 E(K, P) = C 的密钥。

        :param mode: 'process' 多进程并行（默认，可真正利用多核）
                     'thread'  多线程（受 GIL 限制，CPU 密集型任务无法真正并行）
                     'serial'  串行基线（用于性能对照）
        :param repeat: 每个候选密钥的重复验证次数，默认为 1（即正常破解）
        :return: (排序后的密钥列表, 耗时秒数)
        """
        if mode not in ('process', 'thread', 'serial'):
            raise ValueError('不支持的并行模式：%s' % mode)
        if worker_count is None:
            worker_count = os.cpu_count() or 4

        tasks = SDESUtils._build_tasks(plaintext_8bit, ciphertext_8bit, worker_count, repeat)
        found_keys = []

        start_time = time.perf_counter()
        try:
            if mode == 'process':
                with ProcessPoolExecutor(max_workers=len(tasks)) as pool:
                    for hits in pool.map(_scan_key_range, tasks):
                        found_keys.extend(hits)
            elif mode == 'thread':
                with ThreadPoolExecutor(max_workers=len(tasks)) as pool:
                    for hits in pool.map(_scan_key_range, tasks):
                        found_keys.extend(hits)
            else:
                for task in tasks:
                    found_keys.extend(_scan_key_range(task))
        except Exception:
            # 多进程在部分受限环境（如某些 IDE、沙箱）中不可用，自动降级为串行以保证功能可用
            if mode != 'serial':
                return SDESUtils.brute_force(plaintext_8bit, ciphertext_8bit,
                                             worker_count=1, mode='serial', repeat=repeat)
            raise
        elapsed = time.perf_counter() - start_time

        return sorted(found_keys), elapsed

    @staticmethod
    def brute_force_multi(pairs, worker_count=None, mode='process'):
        """给定一个或多个明密文对，返回同时满足全部约束的密钥。

        先用第一对做全空间搜索得到候选集，再用其余各对逐一筛选：
        明密文对越多，越可能把候选密钥收敛到唯一一个。
        """
        if not pairs:
            return [], 0.0
        first_plain, first_cipher = pairs[0]
        candidates, elapsed = SDESUtils.brute_force(first_plain, first_cipher,
                                                    worker_count, mode)
        matched = [k for k in candidates
                   if all(SDESCore.encrypt(p, k) == c for p, c in pairs[1:])]
        return matched, elapsed

    @staticmethod
    def benchmark(plaintext_8bit, ciphertext_8bit, repeat=200):
        """并行性能对照实验：在相同工作量下比较串行 / 多线程 / 多进程三种模式的耗时。

        说明：S-DES 的密钥空间仅 1024，单次破解耗时在毫秒级，进程/线程的启动开销
        会掩盖并行收益。因此本实验通过 repeat 放大“单个密钥的验证代价”，
        从而观察并行化在更大计算量下的真实加速效果。

        :return: [(模式名, 耗时秒, 命中密钥数), ...]
        """
        results = []
        for label, mode in (('串行（单线程）', 'serial'),
                            ('多线程（ThreadPool）', 'thread'),
                            ('多进程（ProcessPool）', 'process')):
            keys, elapsed = SDESUtils.brute_force(plaintext_8bit, ciphertext_8bit,
                                                  mode=mode, repeat=repeat)
            results.append((label, elapsed, len(keys)))
        return results

    @staticmethod
    def find_collisions(plaintext_8bit):
        """密钥碰撞分析：固定明文，遍历全部 1024 个密钥，把密文相同的密钥归为一组。

        :return: {密文: [产生该密文的所有密钥]}，仅保留密钥数大于 1 的碰撞组
        """
        collision_map = defaultdict(list)
        for i in range(KEY_SPACE):
            key = format(i, '010b')
            cipher = SDESCore.encrypt(plaintext_8bit, key)
            collision_map[cipher].append(key)

        return {cipher: keys for cipher, keys in collision_map.items() if len(keys) > 1}

    @staticmethod
    def collision_summary(plaintext_8bit):
        """碰撞情况统计摘要。

        :return: (发生碰撞的密文个数, 卷入碰撞的密钥个数, 单个密文对应的最大密钥数)
        """
        collisions = SDESUtils.find_collisions(plaintext_8bit)
        keys_involved = sum(len(keys) for keys in collisions.values())
        max_group = max((len(keys) for keys in collisions.values()), default=0)
        return len(collisions), keys_involved, max_group


# =================================================================
# 4. GUI 界面模块
# =================================================================
class SDESGUI:
    """图形界面：负责输入校验、事件响应与结果展示，算法逻辑全部委托给 SDESCore / SDESUtils。"""

    def __init__(self, root):
        self.root = root
        self.root.title('S-DES 加解密系统')
        self.root.geometry('760x600')
        self.root.configure(bg='#f0f0f0')

        self.title_font = ('微软雅黑', 16, 'bold')
        self.label_font = ('微软雅黑', 12)
        self.entry_font = ('Consolas', 11)

        # 标题
        tk.Label(root, text='欢迎使用本S-DES加密系统',
                 font=self.title_font, bg='#f0f0f0').pack(pady=18)

        # 输入区域
        input_frame = tk.Frame(root, bg='#f0f0f0')
        input_frame.pack(pady=8)

        # 明文输入
        tk.Label(input_frame, text='明文：', font=self.label_font,
                 bg='#f0f0f0').grid(row=0, column=0, padx=10, pady=5, sticky='ne')
        self.plain_entry = tk.Text(input_frame, font=self.entry_font,
                                   width=45, height=3, wrap='word')
        self.plain_entry.grid(row=0, column=1, padx=10, pady=5)
        self.add_context_menu(self.plain_entry)
        self.set_placeholder(self.plain_entry, '请输入二进制串或任意长度的ASCII字符串')

        # 密钥输入
        tk.Label(input_frame, text='密钥：', font=self.label_font,
                 bg='#f0f0f0').grid(row=1, column=0, padx=10, pady=5, sticky='e')
        self.key_entry = tk.Entry(input_frame, font=self.entry_font, width=45)
        self.key_entry.grid(row=1, column=1, padx=10, pady=5, ipady=3)
        self.add_context_menu(self.key_entry)
        self.set_placeholder(self.key_entry, '请输入10bit密钥')

        # 密文显示 / 输入（可编辑，便于直接粘贴密文进行解密）
        tk.Label(input_frame, text='密文：', font=self.label_font,
                 bg='#f0f0f0').grid(row=2, column=0, padx=10, pady=5, sticky='ne')
        self.cipher_entry = tk.Text(input_frame, font=self.entry_font,
                                    width=45, height=3, wrap='word', bg='#ffffff')
        self.cipher_entry.grid(row=2, column=1, padx=10, pady=5)
        self.add_context_menu(self.cipher_entry)

        # 按钮区
        action_frame = tk.Frame(root, bg='#f0f0f0')
        action_frame.pack(pady=18)

        self.status_label = tk.Label(action_frame, text='', font=('微软雅黑', 10),
                                     fg='blue', bg='#f0f0f0')
        self.status_label.grid(row=0, column=0, padx=12)

        tk.Button(action_frame, text='点击加密', font=('微软雅黑', 11),
                  command=self.do_encrypt, width=12).grid(row=0, column=1, padx=10)
        tk.Button(action_frame, text='点击解密', font=('微软雅黑', 11),
                  command=self.do_decrypt, width=12).grid(row=0, column=2, padx=10)

        # 底部测试区
        bottom_frame = tk.Frame(root, bg='#f0f0f0')
        bottom_frame.pack(side='bottom', pady=15)
        tk.Button(bottom_frame, text='暴力破解测试', command=self.do_brute_force,
                  font=('微软雅黑', 9)).grid(row=0, column=0, padx=8)
        tk.Button(bottom_frame, text='密钥碰撞测试', command=self.do_collision_test,
                  font=('微软雅黑', 9)).grid(row=0, column=1, padx=8)
        tk.Button(bottom_frame, text='并行性能对比', command=self.do_benchmark,
                  font=('微软雅黑', 9)).grid(row=0, column=2, padx=8)

    # ---------------- 界面辅助 ----------------
    def add_context_menu(self, widget):
        """为输入框绑定右键菜单（复制 / 粘贴 / 全选）。"""
        menu = tk.Menu(widget, tearoff=0)
        menu.add_command(label='复制', command=lambda: widget.event_generate('<<Copy>>'))
        menu.add_command(label='粘贴', command=lambda: widget.event_generate('<<Paste>>'))
        menu.add_separator()
        menu.add_command(label='全选', command=lambda: widget.event_generate('<<SelectAll>>'))

        def show_menu(event):
            menu.post(event.x_root, event.y_root)

        widget.bind('<Button-3>', show_menu)

    def set_placeholder(self, widget, text):
        """设置灰色占位提示文字：获得焦点时清空，失去焦点且为空时恢复。"""
        if isinstance(widget, tk.Text):
            widget.insert('1.0', text)
            widget.config(fg='gray')

            def on_focus_in(event):
                if widget.get('1.0', 'end-1c') == text:
                    widget.delete('1.0', 'end')
                    widget.config(fg='black')

            def on_focus_out(event):
                if widget.get('1.0', 'end-1c') == '':
                    widget.insert('1.0', text)
                    widget.config(fg='gray')
        else:
            widget.insert(0, text)
            widget.config(fg='gray')

            def on_focus_in(event):
                if widget.get() == text:
                    widget.delete(0, 'end')
                    widget.config(fg='black')

            def on_focus_out(event):
                if widget.get() == '':
                    widget.insert(0, text)
                    widget.config(fg='gray')

        widget.bind('<FocusIn>', on_focus_in)
        widget.bind('<FocusOut>', on_focus_out)

    def get_plain_text(self):
        """读取明文框内容，占位提示视为空输入。"""
        text = self.plain_entry.get('1.0', 'end-1c').strip()
        if text == '请输入二进制串或任意长度的ASCII字符串':
            return ''
        return text

    def get_cipher_text(self):
        """读取密文框内容。"""
        return self.cipher_entry.get('1.0', 'end-1c').strip()

    def get_input_bits(self, text):
        """把用户输入统一转换为比特串。

        规则：剔除空白字符后若全为 0/1，则按二进制串处理（因此允许分组书写，
        如 '10101010 10101010'）；否则按 ASCII 字符串处理，每字符 8 bit。
        """
        if not text:
            return ''
        compact = ''.join(text.split())          # 去掉所有空白字符（含空格、换行）
        if compact and all(c in '01' for c in compact):
            return compact
        return SDESUtils.str_to_bin(text.strip())

    def check_key(self):
        """校验并读取 10 bit 密钥，非法时弹出提示并返回 None。"""
        key = self.key_entry.get().strip()
        if len(key) != 10 or not all(c in '01' for c in key) or key == '请输入10bit密钥':
            messagebox.showerror('错误', '密钥必须是10位二进制！')
            return None
        return key

    def check_8bit_pair(self):
        """校验暴力破解所需的 8 bit 明文 / 密文，返回 (明文, 密文) 或 None。"""
        plaintext = self.get_input_bits(self.get_plain_text())
        ciphertext = self.get_cipher_text()
        if len(plaintext) != 8:
            messagebox.showwarning('提示', '请在“明文”框输入恰好8位二进制数据！')
            return None
        if len(ciphertext) != 8 or not all(c in '01' for c in ciphertext):
            messagebox.showwarning('提示', '请在“密文”框输入恰好8位二进制密文！')
            return None
        return plaintext, ciphertext

    @staticmethod
    def now():
        """返回当前系统时间字符串，用于给测试结果打时间戳。"""
        return datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')

    # ---------------- 功能回调 ----------------
    def do_encrypt(self):
        """加密：按 8 bit 分组处理，支持二进制串与 ASCII 字符串。"""
        key = self.check_key()
        if key is None:
            return
        plaintext_raw = self.get_plain_text()
        if not plaintext_raw:
            messagebox.showwarning('提示', '请输入要加密的内容！')
            return

        try:
            plaintext = self.get_input_bits(plaintext_raw)
            if not plaintext:
                return
            if len(plaintext) % 8 != 0:
                messagebox.showwarning(
                    '提示', '输入的二进制串长度必须是8的倍数（例如8、16、24位），'
                            '否则无法保证输入输出长度相等！')
                return

            ciphertext = ''
            for i in range(0, len(plaintext), 8):
                ciphertext += SDESCore.encrypt(plaintext[i:i + 8], key)

            self.cipher_entry.delete('1.0', 'end')
            self.cipher_entry.insert('1.0', ciphertext)
            self.status_label.config(
                text='加密完成 (明文%d位，密文%d位)' % (len(plaintext), len(ciphertext)),
                fg='green')
        except Exception as e:
            messagebox.showerror('错误', str(e))

    def do_decrypt(self):
        """解密：结果若可表示为可打印 ASCII 文本则直接还原文本，否则展示二进制串。"""
        key = self.check_key()
        if key is None:
            return
        ciphertext_raw = self.get_cipher_text()
        if not ciphertext_raw:
            messagebox.showwarning('提示', '请先在密文框中输入密文！')
            return
        if len(ciphertext_raw) % 8 != 0:
            messagebox.showerror('错误', '密文长度必须是8的倍数！')
            return

        try:
            plaintext_bits = ''
            for i in range(0, len(ciphertext_raw), 8):
                plaintext_bits += SDESCore.decrypt(ciphertext_raw[i:i + 8], key)

            ascii_str = SDESUtils.bin_to_str(plaintext_bits)
            self.plain_entry.delete('1.0', 'end')
            if SDESUtils.is_printable(ascii_str):
                # 原文是 ASCII 文本（第3关场景）：明文框直接还原为可读文本
                self.plain_entry.insert('1.0', ascii_str)
                self.status_label.config(text='解密完成 (ASCII: %s)' % ascii_str, fg='blue')
            else:
                # 原文是二进制或解密结果为不可见字符：明文框展示二进制串
                self.plain_entry.insert('1.0', plaintext_bits)
                self.status_label.config(text='解密完成 (二进制: %d位)' % len(plaintext_bits),
                                         fg='blue')
            self.plain_entry.config(fg='black')
        except Exception as e:
            messagebox.showerror('错误', str(e))

    def do_brute_force(self):
        """第4关：暴力破解，输出匹配密钥、耗时与系统时间戳。"""
        pair = self.check_8bit_pair()
        if pair is None:
            return
        plaintext, ciphertext = pair

        worker_count = os.cpu_count() or 4
        start_at = self.now()
        found_keys, elapsed = SDESUtils.brute_force(plaintext, ciphertext,
                                                    worker_count=worker_count,
                                                    mode='process')
        end_at = self.now()

        result = '【暴力破解结果】\n'
        result += '已知明文: %s\n' % plaintext
        result += '已知密文: %s\n' % ciphertext
        result += '搜索空间: %d 个密钥\n' % KEY_SPACE
        result += '并行方式: 多进程 (ProcessPool, %d 个 worker)\n\n' % worker_count
        result += '开始时间: %s\n' % start_at
        result += '结束时间: %s\n' % end_at
        result += '耗时: %.4f 秒\n\n' % elapsed

        if found_keys:
            result += '破解成功！共找到 %d 个匹配的密钥:\n' % len(found_keys)
            for k in found_keys:
                result += '  - %s\n' % k
            result += '\n说明：存在多个匹配密钥，说明该明密文对无法唯一确定密钥（第5关结论）。\n'
        else:
            result += '破解失败，未找到匹配的密钥。\n'

        messagebox.showinfo('暴力破解测试', result)

    def do_collision_test(self):
        """第5关：固定明文，统计密钥碰撞情况。"""
        plaintext = self.get_input_bits(self.get_plain_text())
        if len(plaintext) != 8:
            messagebox.showwarning('提示', '请在“明文”框输入恰好8位二进制数据以进行碰撞分析！')
            return

        collisions = SDESUtils.find_collisions(plaintext)
        cipher_count, key_count, max_group = SDESUtils.collision_summary(plaintext)

        result = '【密钥碰撞封闭测试】\n'
        result += '固定明文: %s\n' % plaintext
        result += '测试时间: %s\n\n' % self.now()
        result += '遍历全部 %d 个密钥，其中 %d 个密钥卷入了碰撞，' % (KEY_SPACE, key_count)
        result += '共 %d 个密文由多个密钥产生，单个密文最多对应 %d 个密钥。\n\n' % (
            cipher_count, max_group)

        if collisions:
            result += '碰撞样例（最多展示5组）：\n\n'
            for count, (cipher, keys) in enumerate(collisions.items(), start=1):
                result += '碰撞密文: %s\n' % cipher
                result += '对应的密钥有: %s\n' % ', '.join(keys)
                result += '-' * 40 + '\n'
                if count >= 5:
                    result += '... (仅显示前5组，更多碰撞未展示)\n'
                    break
        else:
            result += '未发现密钥碰撞。\n'

        messagebox.showinfo('密钥碰撞分析', result)

    def do_benchmark(self):
        """第4关附加实验：串行 / 多线程 / 多进程破解耗时对比。"""
        pair = self.check_8bit_pair()
        if pair is None:
            return
        plaintext, ciphertext = pair
        repeat = 100

        # 先刷新界面提示，避免长时间计算时界面看起来像卡死
        self.status_label.config(text='正在测试，请稍候...', fg='gray')
        self.root.update_idletasks()

        results = SDESUtils.benchmark(plaintext, ciphertext, repeat=repeat)
        base_time = results[0][1]

        text = '【并行性能对比实验】\n'
        text += '已知明文: %s  已知密文: %s\n' % (plaintext, ciphertext)
        text += '测试时间: %s\n' % self.now()
        text += '说明：S-DES 密钥空间仅 %d，单次破解仅毫秒级，进程/线程启动开销会掩盖并行收益；\n' % KEY_SPACE
        text += '因此将每个候选密钥的验证代价放大 %d 倍后再对比（工作量相同）。\n\n' % repeat

        for label, elapsed, hit_count in results:
            speedup = base_time / elapsed if elapsed > 0 else 0.0
            text += '%s：%.4f 秒（找到 %d 个密钥，相对串行 %.2fx）\n' % (
                label, elapsed, hit_count, speedup)

        text += '\n结论：多线程受 Python 全局解释器锁（GIL）限制，CPU 密集型任务无法真正并行；\n'
        text += '多进程可绕开 GIL 充分利用多核，但仅在单密钥验证代价足够大时才划算。\n'

        messagebox.showinfo('并行性能对比', text)


if __name__ == '__main__':
    # Windows 下多进程采用 spawn 模式，子进程会重新导入本模块，
    # 因此必须用 __main__ 守卫，避免子进程中重复创建 GUI 窗口。
    root = tk.Tk()
    app = SDESGUI(root)
    root.mainloop()
