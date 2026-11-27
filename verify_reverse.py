#!/usr/bin/env python3
"""Independent all-length check: prepend edges; read MSB first; minimize two DFAs."""
if not __debug__:
    raise SystemExit("Use ordinary Python, not python -O: proof assertions must run")
from itertools import product
from hashlib import sha256
from json import dumps

def reachable(initial,step,accept):
    seq=[initial]; idx={initial:0}; go=[]; final=[]
    for x in seq:
        row=[];final.append(bool(accept(x)))
        for a in range(4):
            y=step(x,a)
            if y not in idx:idx[y]=len(seq);seq.append(y)
            row.append(idx[y])
        go.append(tuple(row))
    return go,final

def canonical(go,final):
    color=list(map(int,final)); rounds=0
    while True:
        sig={};new=[]
        for i,neighbors in enumerate(go):
            key=(final[i],*(color[j] for j in neighbors))
            if key not in sig:sig[key]=len(sig)
            new.append(sig[key])
        rounds+=1
        if new==color:break
        color=new
    reps={k:i for i,k in enumerate(color)};order=[color[0]];ids={color[0]:0};diagram=[]
    for k in order:
        i=reps[k]; row=[]
        for j in go[i]:
            c=color[j]
            if c not in ids:ids[c]=len(order);order.append(c)
            row.append(ids[c])
        diagram.append((final[i],*row))
    return diagram,rounds

def main():
    # State order differs from the forward checker. Track parity via a pair of
    # 18-bit endpoint rows per start rather than a doubled state machine.
    vertices=list(product(range(2),range(3),range(3)));links=[]
    for letter in range(4):
        es=[]
        for c,u,v in vertices:
            edge=[]
            for a,d in product(range(2),repeat=2):
                s=c+a+d
                if (s&1)!=letter//2:continue
                # if u=floor(3x), next state=floor((3a+u)/2); endpoint 1 clamped to state 2.
                X=3*a+u; Y=3*d+v; dest=(s//2,X//2,Y//2)
                flip=(letter&1) and ((X==5)!=(Y==5))
                edge.append((vertices.index(dest),int(flip)))
            assert len(edge)==2;es.append(edge)
        links.append(es)
    def move(m,z):
        # Rows indexed as 2*i+h: reachable ends at parity h. Prepend new edges.
        out=[]
        for (a,p),(d,h) in links[z]:
            out.extend((m[2*a+p]|m[2*d+h],m[2*a+1-p]|m[2*d+1-h]))
        return tuple(out)
    ident=tuple(x for i in range(18) for x in (1<<i,0))
    mats=[ident];indices={ident:0};tab=[];closed=[]
    for m in mats:
        closed.append(any(m[2*i+1]&(1<<i) for i in range(18)));row=[]
        for z in range(4):
            y=move(m,z)
            if y not in indices:indices[y]=len(mats);mats.append(y)
            row.append(indices[y])
        tab.append(row)
    def countlen(k):return k+1 if k<4 else 3 # 0,1,2,odd>=3,even>=4
    g1,f1=reachable((0,0,0),lambda st,z:(tab[st[0]][z],countlen(st[1]),st[2]^(z&1)),
                    lambda st:st[1]==3 and not st[2] and not closed[st[0]])
    # Independent target: in MSB order g has no consecutive 1s, exactly one
    # adjacent 00, and the marked sites are its second zero and the site after it.
    # Triple predicate tests this marking and records counts of 00 and 11.
    def local(a,b,c):
        u,v,w=(z//2 for z in (a,b,c))
        return ((c&1)==((u==v==0) or (v==w==0))) and not(v==w==1), int(v==w==0)
    def targ(st,z):
        k,first,last,zeros,ok,zz=st;k=countlen(k);zeros&=(z%2==0)
        if len(last)==2:
            lv,nn=local(*last,z); ok&=lv;zz=min(2,zz+nn)
        return k,(first+(z,))[:2],(last+(z,))[-2:],zeros,ok,zz
    def acc(st):
        k,first,last,zeros,ok,zz=st
        if k!=3:return False
        if zeros:return True
        for z in first:
            b,plus=local(*last,z);ok&=b;zz+=plus;last=(last[1],z)
        return ok and zz==1
    g2,f2=reachable((0,(),(),True,True,0),targ,acc)
    d1,r1=canonical(g1,f1);d2,r2=canonical(g2,f2)
    assert d1==d2, 'the rooted minimal DFAs differ'
    print(f'prepending monoid={len(tab)}; DFA states={len(g1)},{len(g2)}; refinement rounds={r1},{r2}')
    digest=sha256(dumps(d1,separators=(',',':')).encode()).hexdigest()
    print(f'PASS: identical canonical minimal DFAs ({len(d1)} states), SHA-256={digest}')

if __name__=='__main__':main()
