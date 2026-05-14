import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
from collections import defaultdict

def parse_cfg(text):
    r,nt=[],set()
    lines=[x.strip() for x in text.splitlines() if '->' in x]
    if not lines: raise ValueError("No rules found.")
    start=lines[0].split('->')[0].strip()
    for line in lines:
        A,B=map(str.strip,line.split('->'))
        nt.add(A)
        for alt in B.split('|'):
            rhs=alt.strip().split()
            r.append((A,[] if rhs==['e'] else rhs))
    nts={A for A,_ in r}
    t={x for _,rhs in r for x in rhs if x not in nts}
    return r,nt,t,start

def to_cnf(r,nt,t,start):
    id=[0]
    def new(): id[0]+=1; return f'Y{id[0]}'
    r=[('S0',[start])]+r; start='S0'; nt.add('S0')
    # epsilon
    null=set(A for A,rhs in r if not rhs)
    ch=True
    while ch:
        ch=False
        for A,rhs in r:
            if A not in null and rhs and all(x in null for x in rhs): null.add(A); ch=True
    nr=set()
    for A,rhs in r:
        if not rhs: continue
        pos=[i for i,x in enumerate(rhs) if x in null]
        for m in range(1<<len(pos)):
            t2=rhs[:]
            for b,p in enumerate(pos):
                if m>>b&1: t2[p]=None
            t2=[x for x in t2 if x]
            if t2: nr.add((A,tuple(t2)))
    if start in null: nr.add((start,()))
    r=[(A,list(B)) for A,B in nr]
    # unit
    unit={(A,rhs[0]) for A,rhs in r if len(rhs)==1 and rhs[0] in nt}
    ch=True
    while ch:
        ch=False
        for A,B in list(unit):
            for C,D in list(unit):
                if B==C and (A,D) not in unit: unit.add((A,D)); ch=True
    nr=[(A,rhs) for A,rhs in r if not(len(rhs)==1 and rhs[0] in nt)]
    seen=set((A,tuple(rhs)) for A,rhs in nr)
    for A,B in unit:
        for C,rhs in nr:
            if B==C and (A,tuple(rhs)) not in seen: nr.append((A,rhs)); seen.add((A,tuple(rhs)))
    r=nr
    # useless
    gen=set(t)
    ch=True
    while ch:
        ch=False
        for A,rhs in r:
            if all(x in gen for x in rhs) and A not in gen: gen.add(A); ch=True
    r=[(A,rhs) for A,rhs in r if A in gen and all(x in gen for x in rhs)]
    reach={start}; ch=True
    while ch:
        ch=False
        for A,rhs in r:
            if A in reach:
                for x in rhs:
                    if x not in reach: reach.add(x); ch=True
    r=[(A,rhs) for A,rhs in r if A in reach]
    # terminals
    mp,nr={},[]
    for A,rhs in r:
        if len(rhs)<2: nr.append((A,rhs)); continue
        nr.append((A,[('X_'+x if x in t else x) for x in rhs] if any(x in t for x in rhs) else rhs))
        for x in rhs:
            if x in t and x not in mp: mp[x]=1; nr.append(('X_'+x,[x]))
    r=nr
    # binary
    nr=[]
    for A,rhs in r:
        if len(rhs)<=2: nr.append((A,rhs)); continue
        cur=A
        while len(rhs)>2: y=new(); nr.append((cur,[rhs[0],y])); cur=y; rhs=rhs[1:]
        nr.append((cur,rhs))
    r=nr
    d=defaultdict(list)
    for A,rhs in r: d[A].append(' '.join(rhs) if rhs else 'e')
    cnf_str='\n'.join(f"{A} -> {' | '.join(v)}" for A,v in d.items())
    return r,start,cnf_str

def cyk(r,start,w):
    term=defaultdict(list); bin=defaultdict(list)
    for A,rhs in r:
        if len(rhs)==1: term[rhs[0]].append(A)
        elif len(rhs)==2: bin[tuple(rhs)].append(A)
    n=len(w); T=[[{} for _ in range(n)] for _ in range(n)]
    for i,x in enumerate(w):
        for A in term[x]: T[i][i][A]=x
    for l in range(2,n+1):
        for i in range(n-l+1):
            j=i+l-1
            for k in range(i,j):
                for (B,C),As in bin.items():
                    if B in T[i][k] and C in T[k+1][j]:
                        for A in As: T[i][j][A]=(k,B,C)
    return T

def build(T,i,j,A):
    x=T[i][j][A]
    return (A,x) if isinstance(x,str) else (A,build(T,i,x[0],x[1]),build(T,x[0]+1,j,x[2]))

def tstr(t,d=0):
    if len(t)==2: return ['  '*d+t[0]+'->'+t[1]]
    return ['  '*d+t[0]]+tstr(t[1],d+1)+tstr(t[2],d+1)

def deriv(t):
    out=[[t[0]]]
    def go(n,s):
        if len(n)==2: return s
        i=s.index(n[0]); s=s[:i]+[n[1][0],n[2][0]]+s[i+1:]; out.append(s[:])
        s=go(n[1],s); s=go(n[2],s); return s
    go(t,[t[0]]); return ['Leftmost Derivation:']+['=>'+' '.join(x) for x in out]

class Node:
    def __init__(self,t):
        self.label=t[0]; self._x=self._y=self._w=0
        if len(t)==2: self.leaf=t[1]; self.left=self.right=None
        else: self.leaf=None; self.left=Node(t[1]); self.right=Node(t[2])

def layout(root):
    c=[0]
    def ax(n):
        if n.leaf is not None: n._x=c[0];n._w=1;c[0]+=1;return
        ax(n.left);ax(n.right);n._x=(n.left._x+n.right._x)/2;n._w=n.left._w+n.right._w
    def ay(n,d=0):
        n._y=d
        if n.left: ay(n.left,d+1);ay(n.right,d+1)
    ax(root);ay(root);return c[0]

def draw(canvas,tup):
    canvas.delete('all'); root=Node(tup); total=layout(root)
    W=canvas.winfo_width() or 600; PAD=40; R=20; LH=70
    def cx(n): return PAD+n._x*(W-2*PAD)/max(total-1,1)
    def cy(n): return PAD+n._y*LH
    def rec(n):
        x,y=cx(n),cy(n)
        if n.left:
            canvas.create_line(x,y,cx(n.left),cy(n.left),fill='#888',width=1.5)
            canvas.create_line(x,y,cx(n.right),cy(n.right),fill='#888',width=1.5)
            rec(n.left);rec(n.right)
            canvas.create_oval(x-R,y-R,x+R,y+R,fill='#e8e8f0',outline='#9090c0',width=1.5)
            canvas.create_text(x,y,text=n.label,font=('Courier',11,'bold'),fill='#222')
        else:
            canvas.create_rectangle(x-R,y-10,x+R,y+10,fill='#d0eaff',outline='#5090cc')
            canvas.create_text(x,y,text=n.leaf,font=('Courier',10),fill='#1a4a80')
            canvas.create_text(x,y+22,text=n.label,font=('Courier',9),fill='#666')
    rec(root)

class App(tk.Tk):
    def __init__(self):
        super().__init__(); self.title("CFG/CYK Parser"); self.geometry("900x700")
        self.configure(bg='#f5f5f7'); self._tr=None; self._build()
    def _build(self):
        tk.Label(self,text="CFG / CYK Parser",font=('Helvetica',16,'bold'),bg='#f5f5f7').pack(anchor='w',padx=16,pady=8)
        inp=tk.Frame(self,bg='#f5f5f7',padx=16); inp.pack(fill='x')
        lf=tk.LabelFrame(inp,text="Grammar",bg='#f5f5f7',padx=6,pady=4); lf.pack(side='left',fill='both',expand=True,padx=(0,8))
        self.gb=scrolledtext.ScrolledText(lf,width=36,height=7,font=('Courier',11),relief='flat',bg='#fff'); self.gb.pack(fill='both',expand=True)
        self.gb.insert('1.0',"S -> A B A\nA -> a A | e\nB -> b B c | e")
        r=tk.Frame(inp,bg='#f5f5f7'); r.pack(side='left',fill='both',expand=True)
        lf2=tk.LabelFrame(r,text="Input String",bg='#f5f5f7',padx=6,pady=4); lf2.pack(fill='x',pady=(0,6))
        self.se=tk.Entry(lf2,font=('Courier',12),relief='flat',bg='#fff'); self.se.pack(fill='x'); self.se.insert(0,"a b c")
        bf=tk.Frame(r,bg='#f5f5f7'); bf.pack(fill='x',pady=4)
        tk.Button(bf,text="Parse",command=self.run,bg='#2a2a5a',fg='white',font=('Helvetica',11,'bold'),relief='flat',padx=16,pady=4,cursor='hand2').pack(side='left',padx=(0,8))
        tk.Button(bf,text="Clear",command=self.clear,bg='#e0e0e8',fg='#333',relief='flat',padx=12,pady=4,cursor='hand2').pack(side='left')
        self.sv=tk.StringVar(); self.sl=tk.Label(r,textvariable=self.sv,font=('Helvetica',12,'bold'),bg='#f5f5f7'); self.sl.pack(fill='x')
        ef=tk.LabelFrame(r,text="Examples",bg='#f5f5f7',padx=6,pady=2); ef.pack(fill='x')
        for lbl,g,s in [("a b c","S -> A B A\nA -> a A | e\nB -> b B c | e","a b c"),("b b c c","S -> A B A\nA -> a A | e\nB -> b B c | e","b b c c"),("a a b b","S -> a S b | e","a a b b"),("ab ab","S -> S S | a b","a b a b")]:
            tk.Button(ef,text=lbl,relief='flat',bg='#dde',font=('Helvetica',9),padx=4,pady=1,cursor='hand2',command=lambda g=g,s=s:(self.gb.delete('1.0','end'),self.gb.insert('1.0',g),self.se.delete(0,'end'),self.se.insert(0,s))).pack(side='left',padx=2)
        nb=ttk.Notebook(tk.Frame(self,bg='#f5f5f7',padx=16,pady=8)); nb.master.pack(fill='both',expand=True); nb.pack(fill='both',expand=True)
        self.nb=nb
        t1=tk.Frame(nb,bg='#fff'); nb.add(t1,text='  Parse Tree  ')
        self.cv=tk.Canvas(t1,bg='#fafafa',relief='flat'); vsb=ttk.Scrollbar(t1,orient='vertical',command=self.cv.yview); hsb=ttk.Scrollbar(t1,orient='horizontal',command=self.cv.xview)
        self.cv.configure(yscrollcommand=vsb.set,xscrollcommand=hsb.set); vsb.pack(side='right',fill='y'); hsb.pack(side='bottom',fill='x'); self.cv.pack(fill='both',expand=True)
        self.cv.bind('<Configure>',lambda e:draw(self.cv,self._tr) if self._tr else None)
        self.db,self.cb,self.tb=self._tab(nb,'  Derivation  '),self._tab(nb,'  CNF Grammar  '),self._tab(nb,'  Tree (text)  ')
    def _tab(self,nb,name):
        f=tk.Frame(nb,bg='#fff'); nb.add(f,text=name)
        b=scrolledtext.ScrolledText(f,font=('Courier',11),wrap='none',relief='flat',bg='#fafafa'); b.pack(fill='both',expand=True,padx=8,pady=8); return b
    def _set(self,w,txt): w.config(state='normal'); w.delete('1.0','end'); w.insert('1.0',txt); w.config(state='disabled')
    def clear(self):
        self.sv.set(''); self.sl.config(fg='#333'); self.cv.delete('all'); self._tr=None
        for b in(self.db,self.cb,self.tb): b.config(state='normal'); b.delete('1.0','end')
    def run(self):
        self.clear()
        try:
            r,nt,t,start=parse_cfg(self.gb.get('1.0','end').strip())
            r,start,cnf_str=to_cnf(r,nt,t,start)
            self._set(self.cb,cnf_str)
            w=self.se.get().strip().split() if self.se.get().strip() else []
            if not w:
                ok=any(A==start and not rhs for A,rhs in r)
                self.sv.set("✓ ACCEPTED (empty)" if ok else "✗ REJECTED"); self.sl.config(fg='#1a7a1a' if ok else '#aa1a1a'); return
            T=cyk(r,start,w)
            if start in T[0][len(w)-1]:
                self.sv.set("✓ ACCEPTED"); self.sl.config(fg='#1a7a1a')
                tr=build(T,0,len(w)-1,start); self._tr=tr
                self.update_idletasks(); draw(self.cv,tr); self.nb.select(0)
                self._set(self.tb,'\n'.join(tstr(tr))); self._set(self.db,'\n'.join(deriv(tr)))
            else:
                self.sv.set("✗ REJECTED"); self.sl.config(fg='#aa1a1a')
                self._set(self.db,"String not in language."); self._set(self.tb,"No parse tree.")
        except Exception as e: messagebox.showerror("Error",str(e))

App().mainloop()
