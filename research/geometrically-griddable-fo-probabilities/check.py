#!/usr/bin/env python3
"""Finite sanity checks. Python 3 stdlib only; not the proof of the theorem."""
from itertools import combinations,product
from collections import Counter
from fractions import Fraction as F
from math import comb

def require(x):
    if not x: raise ValueError('failed exact check')

def orders():
    total=0
    for n in range(1,6):
        pairs=list(combinations(range(n),2)); seen=set()
        for mask in range(1<<len(pairs)):
            pred=[0]*n
            for i,(u,v) in enumerate(pairs):
                if mask>>i&1: pred[v]|=1<<u
            for v in range(n):
                for u in range(v):
                    if (pred[v]>>u)&1: pred[v]|=pred[u]
            key=tuple(pred)
            if key in seen: continue
            seen.add(key)
            for lab in product(range(3),repeat=n):
                if any(lab[u]==lab[v] and not (pred[v]>>u)&1 for u,v in pairs):continue
                def phase(nodes,a):
                    if not nodes:return []
                    require(a>=0)
                    hmask=sum(1<<i for i in nodes if lab[i]==a)
                    blocks={}
                    for i in nodes:blocks.setdefault(pred[i]&hmask,[]).append(i)
                    out=[]
                    for k,ix in sorted(blocks.items()):
                        own=[i for i in ix if lab[i]==a]; require(len(own)<=1)
                        out+=phase([i for i in ix if lab[i]!=a],a-1)+own
                    return out
                direct=[]; alive=(1<<n)-1
                while alive:
                    i=min((i for i in range(n) if alive>>i&1 and not (pred[i]&alive)),key=lambda i:lab[i])
                    direct.append(i);alive^=1<<i
                require(phase(list(range(n)),2)==direct);total+=1
    print('Label-chain posets and greedy/rank-block comparisons:',total)

def race():
    suites=0; words=0
    for q in range(2,12):
        w=['aab'+'b'*j+'a'+'b'*(q+1-j) for j in range(q)]
        require(len(set(w))==q)
        for u,v in product(w,repeat=2):require(all(u[-i:]!=v[:i] for i in range(1,len(u))))
        # Realize each a as a one-edge self-loop and b as a two-edge return.
        w=[u.replace('a','0').replace('b','12') for u in w];L=len(w[0])
        prefixes={v[:k] for v in w for k in range(len(v))}
        states=Counter({(0,'',-1):1})
        for h in range(1,2*L+6):
            nxt=Counter()
            for (state,prefix,typ),ct in states.items():
                for sym,dest in ([('0',0),('1',1)] if state==0 else [('2',0)]):
                    p=prefix+sym;t=typ
                    if typ<0 and p in w:t=w.index(p)
                    if t>=0:p=''
                    else:
                        while p not in prefixes:p=p[1:]
                    nxt[dest,p,t]+=ct
            states=nxt
            if h>=L:
                for dest in range(2):
                    counts=[states[dest,'',j] for j in range(q)]
                    require(len(set(counts))==1);words+=sum(counts)
                suites+=1
    print('Golden-mean edge-walk die, equal counts by terminal state:',suites,'horizons;',words,'marked walks across tests')

def bernstein():
    cases=0
    for coeff in [(F(13,50),-1,1),(F(2,3),F(-1,6)),(F(1,8),0,F(1,4))]:
        for n in (31,71):
            c=[sum(a*F(comb(k,j),comb(n,j)) for j,a in enumerate(coeff)) for k in range(n+1)]
            require(all(0<x<1 for x in c))
            for t in [F(i,9) for i in range(10)]:
                require(sum(comb(n,k)*t**k*(1-t)**(n-k)*c[k] for k in range(n+1))==sum(a*t**j for j,a in enumerate(coeff)));cases+=1
    # Q(phi) pairs A+B*phi with phi^2=1+phi.  At the golden-mean loop vertex
    # five closed 4-edge paths exist; choosing any two gives p=2/phi^4.
    def mul(x,y):
        a,b=x;c,d=y;return (a*c+b*d,a*d+b*c+b*d)
    phi4=mul((1,1),(1,1));p=(10,-6);require(mul(phi4,p)==(2,0))
    require((F(2,3)-F(p[0],6),-F(p[1],6))==(-1,1))
    print('Bernstein evaluations:',cases,'and exact golden-ratio target checked')
if __name__=='__main__':orders();race();bernstein()
