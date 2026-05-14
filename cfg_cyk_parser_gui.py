import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
from collections import defaultdict
import math


# ---------------- CFG ----------------

class CFG:
    def __init__(self, text):
        self.r, self.nt, self.t = [], set(), set()
        lines = [x.strip() for x in text.splitlines() if '->' in x]
        if not lines:
            raise ValueError("No valid rules found. Use '->' notation.")
        self.start = lines[0].split('->')[0].strip()
        for line in lines:
            A, B = map(str.strip, line.split('->'))
            self.nt.add(A)
            for alt in B.split('|'):
                rhs = alt.strip().split()
                rhs = [] if rhs == ['e'] else rhs
                self.r.append((A, rhs))
        nts = {A for A, _ in self.r}
        for _, rhs in self.r:
            for x in rhs:
                if x not in nts:
                    self.t.add(x)

    def show(self):
        d = defaultdict(list)
        for A, rhs in self.r:
            d[A].append(' '.join(rhs) if rhs else 'e')
        return '\n'.join(f"{A} -> {' | '.join(alts)}" for A, alts in d.items())


# ---------------- CNF ----------------

class CNF:
    def __init__(self, g):
        self.g = g
        self.id = 0

    def new(self):
        self.id += 1
        return f'Y{self.id}'

    def step1(self):
        g = self.g
        g.r = [('S0', [g.start])] + g.r
        g.start = 'S0'
        g.nt.add('S0')

    def step2(self):
        g = self.g
        null = set(A for A, rhs in g.r if not rhs)
        changed = True
        while changed:
            changed = False
            for A, rhs in g.r:
                if A not in null and rhs and all(x in null for x in rhs):
                    null.add(A)
                    changed = True
        nr = set()
        for A, rhs in g.r:
            if not rhs:
                continue
            pos = [i for i, x in enumerate(rhs) if x in null]
            for m in range(1 << len(pos)):
                t = rhs[:]
                for b, p in enumerate(pos):
                    if m >> b & 1:
                        t[p] = None
                t = [x for x in t if x]
                if t:
                    nr.add((A, tuple(t)))
        if g.start in null:
            nr.add((g.start, tuple()))
        g.r = [(A, list(B)) for A, B in nr]

    def step3(self):
        g = self.g
        unit = {(A, rhs[0]) for A, rhs in g.r
                if len(rhs) == 1 and rhs[0] in g.nt}
        changed = True
        while changed:
            changed = False
            for A, B in list(unit):
                for C, D in list(unit):
                    if B == C and (A, D) not in unit:
                        unit.add((A, D))
                        changed = True
        nr = [(A, rhs) for A, rhs in g.r
              if not (len(rhs) == 1 and rhs[0] in g.nt)]
        seen = set((A, tuple(rhs)) for A, rhs in nr)
        for A, B in unit:
            for C, rhs in nr:
                if B == C and (A, tuple(rhs)) not in seen:
                    nr.append((A, rhs))
                    seen.add((A, tuple(rhs)))
        g.r = nr

    def step4(self):
        g = self.g
        gen = set(g.t)
        changed = True
        while changed:
            changed = False
            for A, rhs in g.r:
                if all(x in gen for x in rhs) and A not in gen:
                    gen.add(A)
                    changed = True
        g.r = [(A, rhs) for A, rhs in g.r
               if A in gen and all(x in gen for x in rhs)]
        reach = {g.start}
        changed = True
        while changed:
            changed = False
            for A, rhs in g.r:
                if A in reach:
                    for x in rhs:
                        if x not in reach:
                            reach.add(x)
                            changed = True
        g.r = [(A, rhs) for A, rhs in g.r if A in reach]

    def step5a(self):
        g = self.g
        mp, nr = {}, []
        for A, rhs in g.r:
            if len(rhs) < 2:
                nr.append((A, rhs))
                continue
            t = []
            for x in rhs:
                if x in g.t:
                    if x not in mp:
                        mp[x] = f'X_{x}'
                    t.append(mp[x])
                else:
                    t.append(x)
            nr.append((A, t))
        for x, y in mp.items():
            nr.append((y, [x]))
        g.r = nr

    def step5b(self):
        g = self.g
        nr = []
        for A, rhs in g.r:
            if len(rhs) <= 2:
                nr.append((A, rhs))
                continue
            cur = A
            while len(rhs) > 2:
                y = self.new()
                nr.append((cur, [rhs[0], y]))
                cur = y
                rhs = rhs[1:]
            nr.append((cur, rhs))
        g.r = nr

    def convert(self):
        self.step1()
        self.step2()
        self.step3()
        self.step4()
        self.step5a()
        self.step5b()
        return self.g


# ---------------- CYK ----------------

class CYK:
    def __init__(self, g):
        self.g = g
        self.term = defaultdict(list)
        self.bin = defaultdict(list)
        for A, rhs in g.r:
            if len(rhs) == 1:
                self.term[rhs[0]].append(A)
            elif len(rhs) == 2:
                self.bin[tuple(rhs)].append(A)

    def parse(self, w):
        n = len(w)
        T = [[{} for _ in range(n)] for _ in range(n)]
        for i, x in enumerate(w):
            for A in self.term[x]:
                T[i][i][A] = x
        for l in range(2, n + 1):
            for i in range(n - l + 1):
                j = i + l - 1
                for k in range(i, j):
                    for (B, C), As in self.bin.items():
                        if B in T[i][k] and C in T[k + 1][j]:
                            for A in As:
                                T[i][j][A] = (k, B, C)
        return T


# ---------------- TREE ----------------

def build_tree(T, i, j, A):
    x = T[i][j][A]
    if isinstance(x, str):
        return (A, x)
    k, B, C = x
    return (A, build_tree(T, i, k, B), build_tree(T, k + 1, j, C))


def tree_to_str(t, d=0):
    lines = []
    if len(t) == 2:
        lines.append('  ' * d + t[0] + ' -> ' + t[1])
    else:
        lines.append('  ' * d + t[0])
        lines.extend(tree_to_str(t[1], d + 1))
        lines.extend(tree_to_str(t[2], d + 1))
    return lines


def derive(t):
    out = [[t[0]]]

    def go(node, sent):
        if len(node) == 2:
            return sent
        A = node[0]
        i = sent.index(A)
        rep = [node[1][0], node[2][0]]
        sent = sent[:i] + rep + sent[i + 1:]
        out.append(sent[:])
        sent = go(node[1], sent)
        sent = go(node[2], sent)
        return sent

    go(t, [t[0]])
    lines = ["Leftmost Derivation:"]
    for x in out:
        lines.append("=> " + ' '.join(x))
    return lines


# ---------------- TREE CANVAS ----------------

def layout_tree(node):
    counter = [0]

    def assign_x(n):
        if len(n) == 2:
            n._x = counter[0]
            n._w = 1
            counter[0] += 1
            return
        assign_x(n[1])
        assign_x(n[2])
        n._x = (n[1]._x + n[2]._x) / 2
        n._w = n[1]._w + n[2]._w

    def assign_y(n, d=0):
        n._y = d
        if len(n) > 2:
            assign_y(n[1], d + 1)
            assign_y(n[2], d + 1)

    # Convert tuple tree to list-based mutable objects
    class Node:
        def __init__(self, t):
            self.label = t[0]
            if len(t) == 2:
                self.leaf = t[1]
                self.left = self.right = None
            else:
                self.leaf = None
                self.left = Node(t[1])
                self.right = Node(t[2])
            self._x = self._y = self._w = 0

        def __len__(self):
            return 2 if self.left is None else 3

        def __getitem__(self, i):
            if i == 0: return self.label
            if i == 1: return self.left
            if i == 2: return self.right

    root = Node(node)

    def ax(n):
        if n.leaf is not None:
            n._x = counter[0]; n._w = 1; counter[0] += 1; return
        ax(n.left); ax(n.right)
        n._x = (n.left._x + n.right._x) / 2
        n._w = n.left._w + n.right._w

    def ay(n, d=0):
        n._y = d
        if n.left: ay(n.left, d+1)
        if n.right: ay(n.right, d+1)

    ax(root); ay(root)
    return root, counter[0]


def draw_tree_on_canvas(canvas, node_tuple):
    canvas.delete("all")
    root, total = layout_tree(node_tuple)

    PAD = 40
    NODE_R = 20
    LEVEL_H = 70

    cw = canvas.winfo_width() or 600
    ch = canvas.winfo_height() or 400

    def cx(n): return PAD + n._x * (cw - 2*PAD) / max(total - 1, 1)
    def cy(n): return PAD + n._y * LEVEL_H

    # Compute required height
    max_y = [0]
    def get_max_y(n):
        if n._y > max_y[0]: max_y[0] = n._y
        if n.left: get_max_y(n.left)
        if n.right: get_max_y(n.right)
    get_max_y(root)
    needed_h = PAD + max_y[0] * LEVEL_H + PAD + 30
    canvas.config(scrollregion=(0, 0, cw, needed_h))

    def draw(n):
        x, y = cx(n), cy(n)
        if n.left:
            lx, ly = cx(n.left), cy(n.left)
            rx, ry = cx(n.right), cy(n.right)
            canvas.create_line(x, y, lx, ly, fill='#888', width=1.5)
            canvas.create_line(x, y, rx, ry, fill='#888', width=1.5)
            draw(n.left)
            draw(n.right)
            canvas.create_oval(x-NODE_R, y-NODE_R, x+NODE_R, y+NODE_R,
                               fill='#e8e8f0', outline='#9090c0', width=1.5)
            canvas.create_text(x, y, text=n.label, font=('Courier', 11, 'bold'), fill='#222')
        else:
            canvas.create_rectangle(x-NODE_R, y-10, x+NODE_R, y+10,
                                    fill='#d0eaff', outline='#5090cc', width=1)
            canvas.create_text(x, y, text=n.leaf, font=('Courier', 10), fill='#1a4a80')
            canvas.create_text(x, y+22, text=n.label, font=('Courier', 9), fill='#666')

    draw(root)


# ---------------- GUI ----------------

class ParserApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("CFG Parser — CNF + CYK")
        self.geometry("900x700")
        self.configure(bg='#f5f5f7')
        self._tree_tuple = None
        self._build_ui()

    def _build_ui(self):
        # ---- Top bar ----
        top = tk.Frame(self, bg='#f5f5f7', pady=10, padx=16)
        top.pack(fill='x')
        tk.Label(top, text="CFG / CYK Parser", font=('Helvetica', 16, 'bold'),
                 bg='#f5f5f7', fg='#1a1a2e').pack(side='left')

        # ---- Input pane ----
        inp = tk.Frame(self, bg='#f5f5f7', padx=16)
        inp.pack(fill='x')

        # Grammar
        lf1 = tk.LabelFrame(inp, text="Grammar", font=('Helvetica', 10),
                             bg='#f5f5f7', fg='#444', padx=8, pady=6)
        lf1.pack(side='left', fill='both', expand=True, padx=(0,8))
        self.grammar_box = scrolledtext.ScrolledText(lf1, width=38, height=7,
                                                     font=('Courier', 11), wrap='word',
                                                     relief='flat', bd=1,
                                                     bg='#ffffff', fg='#111')
        self.grammar_box.pack(fill='both', expand=True)
        self.grammar_box.insert('1.0', "S -> A B A\nA -> a A | e\nB -> b B c | e")

        # Right side: string + buttons + examples
        right = tk.Frame(inp, bg='#f5f5f7')
        right.pack(side='left', fill='both', expand=True)

        lf2 = tk.LabelFrame(right, text="Input String (space-separated)", font=('Helvetica', 10),
                              bg='#f5f5f7', fg='#444', padx=8, pady=6)
        lf2.pack(fill='x', pady=(0,6))
        self.str_entry = tk.Entry(lf2, font=('Courier', 12), relief='flat', bd=1, bg='#fff')
        self.str_entry.pack(fill='x')
        self.str_entry.insert(0, "a b c")

        # Buttons
        btn_frame = tk.Frame(right, bg='#f5f5f7')
        btn_frame.pack(fill='x', pady=4)
        tk.Button(btn_frame, text="Parse", command=self.run_parser,
                  bg='#2a2a5a', fg='white', font=('Helvetica', 11, 'bold'),
                  relief='flat', padx=18, pady=5, cursor='hand2').pack(side='left', padx=(0,8))
        tk.Button(btn_frame, text="Clear", command=self.clear_output,
                  bg='#e0e0e8', fg='#333', font=('Helvetica', 10),
                  relief='flat', padx=12, pady=5, cursor='hand2').pack(side='left')

        # Status label
        self.status_var = tk.StringVar()
        self.status_lbl = tk.Label(right, textvariable=self.status_var,
                                   font=('Helvetica', 12, 'bold'),
                                   bg='#f5f5f7', fg='#333')
        self.status_lbl.pack(fill='x', pady=4)

        # Examples
        ex_frame = tk.LabelFrame(right, text="Examples", font=('Helvetica', 10),
                                  bg='#f5f5f7', fg='#444', padx=8, pady=4)
        ex_frame.pack(fill='x')
        examples = [
            ("a b c",  "S -> A B A\nA -> a A | e\nB -> b B c | e",  "a b c"),
            ("b b c c","S -> A B A\nA -> a A | e\nB -> b B c | e",  "b b c c"),
            ("a a b b","S -> a S b | e",                             "a a b b"),
            ("ab ab",  "S -> S S | a b",                            "a b a b"),
        ]
        for label, gram, s in examples:
            tk.Button(ex_frame, text=label, relief='flat', bg='#dde', fg='#222',
                      font=('Helvetica', 9), padx=6, pady=2, cursor='hand2',
                      command=lambda g=gram, st=s: self.load_example(g, st)
                      ).pack(side='left', padx=2)

        # ---- Notebook ----
        nb_frame = tk.Frame(self, bg='#f5f5f7', padx=16, pady=8)
        nb_frame.pack(fill='both', expand=True)

        self.nb = ttk.Notebook(nb_frame)
        self.nb.pack(fill='both', expand=True)
        style = ttk.Style()
        style.configure('TNotebook', background='#f5f5f7')
        style.configure('TNotebook.Tab', font=('Helvetica', 10))

        # Tab 1: Parse Tree (canvas)
        t1 = tk.Frame(self.nb, bg='#fff')
        self.nb.add(t1, text='  Parse Tree  ')
        self.canvas = tk.Canvas(t1, bg='#fafafa', relief='flat', bd=0)
        vsb = ttk.Scrollbar(t1, orient='vertical', command=self.canvas.yview)
        hsb = ttk.Scrollbar(t1, orient='horizontal', command=self.canvas.xview)
        self.canvas.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.pack(side='right', fill='y')
        hsb.pack(side='bottom', fill='x')
        self.canvas.pack(fill='both', expand=True)
        self.canvas.bind('<Configure>', self._redraw_tree)

        # Tab 2: Derivation
        t2 = tk.Frame(self.nb, bg='#fff')
        self.nb.add(t2, text='  Derivation  ')
        self.deriv_box = scrolledtext.ScrolledText(t2, font=('Courier', 11),
                                                   wrap='none', relief='flat',
                                                   bg='#fafafa', fg='#111')
        self.deriv_box.pack(fill='both', expand=True, padx=8, pady=8)

        # Tab 3: CNF
        t3 = tk.Frame(self.nb, bg='#fff')
        self.nb.add(t3, text='  CNF Grammar  ')
        self.cnf_box = scrolledtext.ScrolledText(t3, font=('Courier', 11),
                                                  wrap='none', relief='flat',
                                                  bg='#fafafa', fg='#111')
        self.cnf_box.pack(fill='both', expand=True, padx=8, pady=8)

        # Tab 4: Parse Tree (text)
        t4 = tk.Frame(self.nb, bg='#fff')
        self.nb.add(t4, text='  Tree (text)  ')
        self.tree_box = scrolledtext.ScrolledText(t4, font=('Courier', 11),
                                                   wrap='none', relief='flat',
                                                   bg='#fafafa', fg='#111')
        self.tree_box.pack(fill='both', expand=True, padx=8, pady=8)

    def load_example(self, gram, s):
        self.grammar_box.delete('1.0', 'end')
        self.grammar_box.insert('1.0', gram)
        self.str_entry.delete(0, 'end')
        self.str_entry.insert(0, s)

    def clear_output(self):
        self.status_var.set('')
        self.status_lbl.config(fg='#333')
        self.canvas.delete('all')
        self._tree_tuple = None
        for box in (self.deriv_box, self.cnf_box, self.tree_box):
            box.config(state='normal')
            box.delete('1.0', 'end')

    def _set_text(self, widget, text):
        widget.config(state='normal')
        widget.delete('1.0', 'end')
        widget.insert('1.0', text)
        widget.config(state='disabled')

    def _redraw_tree(self, event=None):
        if self._tree_tuple:
            draw_tree_on_canvas(self.canvas, self._tree_tuple)

    def run_parser(self):
        self.clear_output()
        grammar_text = self.grammar_box.get('1.0', 'end').strip()
        str_text = self.str_entry.get().strip()

        try:
            g = CFG(grammar_text)
            cnf = CNF(g).convert()
            self._set_text(self.cnf_box, cnf.show())

            w = str_text.split() if str_text else []

            if len(w) == 0:
                has_eps = any(A == cnf.start and not rhs for A, rhs in cnf.r)
                if has_eps:
                    self.status_var.set("✓ ACCEPTED (empty string)")
                    self.status_lbl.config(fg='#1a7a1a')
                else:
                    self.status_var.set("✗ REJECTED")
                    self.status_lbl.config(fg='#aa1a1a')
                return

            T = CYK(cnf).parse(w)
            accepted = cnf.start in T[0][len(w)-1]

            if accepted:
                self.status_var.set("✓  ACCEPTED")
                self.status_lbl.config(fg='#1a7a1a')

                tr = build_tree(T, 0, len(w)-1, cnf.start)
                self._tree_tuple = tr

                # Draw visual tree
                self.update_idletasks()
                draw_tree_on_canvas(self.canvas, tr)
                self.nb.select(0)

                # Text tree
                self._set_text(self.tree_box, '\n'.join(tree_to_str(tr)))

                # Derivation
                self._set_text(self.deriv_box, '\n'.join(derive(tr)))

            else:
                self.status_var.set("✗  REJECTED")
                self.status_lbl.config(fg='#aa1a1a')
                self._set_text(self.deriv_box, "String not in language — no derivation.")
                self._set_text(self.tree_box, "No parse tree — string was rejected.")

        except Exception as e:
            messagebox.showerror("Error", str(e))


if __name__ == '__main__':
    app = ParserApp()
    app.mainloop()
