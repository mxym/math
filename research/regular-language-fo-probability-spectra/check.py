#!/usr/bin/env python3
"""Exhaust small right-deterministic cyclic components, and literal crossings."""
from itertools import product
from collections import deque,Counter
from fractions import Fraction as F
def require(ok):
    if not ok:raise RuntimeError('exact check failed')
def nxt(t,S,a):
    return frozenset(t[i][a] for i in S if t[i][a]>=0)
def walk(t,S,w):
    for a in w:S=nxt(t,S,a)
    return S
def autos(n):
    for arr in product(range(-1,n),repeat=2*n):
        t=[arr[2*i:2*i+2] for i in range(n)]
        if max(sum(y>=0 for y in x) for x in t)<=1:continue
        for s in range(n):
            S={s}
            for _ in range(n):S|={y for x in list(S) for y in t[x] if y>=0}
            if len(S)<n:break
        else:yield t
def minrank(t):
    Q=frozenset(range(len(t)));seen={Q:()};todo=deque([Q])
    while todo:
        S=todo.popleft()
        for a in range(2):
            V=nxt(t,S,a)
            if V and V not in seen:seen[V]=seen[S]+(a,);todo.append(V)
    return min(map(len,seen)),seen
def checker(n):
    cases=hidden=0;marks=walks=0
    for t in autos(n):
        cases+=1;d,seen=minrank(t);hidden+=d>1
        for S,b in seen.items():
            if len(S)!=d:continue
            marks+=1
            for l in range(5):
                for w in product(range(2),repeat=l):
                    images=[walk(t,{i},w) for i in S]
                    require(len(set(map(bool,images)))==1)
                    if images[0]:require(len(set.union(set(),*(set(i) for i in images)))==d)
                    walks+=1
        # Enumerate the row-wise counts via adjacency iterates without relying on the image test.
        cnt=[1]*n
        for _ in range(8):
            cnt=[sum(cnt[y] for y in row if y>=0) for row in t]
            for S in seen:
                if len(S)==d:require(len({cnt[i] for i in S})==1)
    return cases,hidden,marks,walks
def markers():
    # language a* [e] (0,1)* [f] (0,2)* with two tied but unequal factor languages,
    # and a candidate marker straddling the entrance (cross edge may itself print 1).
    marks=['1'*5,'2'*5];v=0;bridges=0
    for small in ('','0','00','000'):
        for crossing in ('0','1','2'):
            for w in product('012',repeat=8):
                if '1' in w and '2' in w:continue
                w=''.join(w);tag='2' if '2' in w else '1';text=small+crossing+w
                hit=[(text.index(m)+len(m),m) for m in marks if m in text]
                if hit:
                    end,m=min(hit);require(m[0]==tag and end>len(small)+len(crossing))
                    require(text[end-1]==tag);v+=1
                    if end-len(m)<len(small)+len(crossing):bridges+=1
    return v,bridges
def overlapping():
    # Two hidden copies of the full binary shift; both letters toggle a hidden phase differently.
    # b=00 permits the shortest return 0, overlapping the preceding occurrence.
    h=16;z=Counter()
    for s in product('01',repeat=h):
        s=''.join(s);idx=('00'+s).find('00',1)
        if idx>=0:z[s[:idx]]+=1
    require(z['0']==2**(h-1) and z['100']==2**(h-3))
    for w,ct in z.items():require(F(ct,2**h)==F(1,2**len(w)))
    print('Overlapping marker: exact probabilities of',len(z),'distinct first-return strings through length',h)
def phase_example():
    for n in range(4,242):
        counts=[sum(1 for i in range(n) if i%4==0) for _ in range(2)]
        counts += [0 if n%2 else sum(1 for i in range(n) if i%4<2)]
        weights=(F(1,2),F(1,2),F(0)) if n%2 else (F(1,4),F(1,4),F(1,2))
        for c,w in zip(counts,weights):require(abs(F(c,sum(counts))-w)<=F(4,n))
    w1=(F(1,4),F(1,4),F(1,2));w2=(F(1,2),F(1,2),F(0))
    dots=lambda w,x:sum(a*b for a,b in zip(w,x))
    V=list(product(range(2),repeat=3));require(({dots(w1,x) for x in V}&{dots(w2,x) for x in V})=={0,F(1,2),1})
    require({dots(w1,x) for x in V if dots(w1,x)==dots(w2,x)}=={0,1})
    print('Shared phase-atom example: 238 cardinalities and all 8 Boolean selectors checked')
if __name__=='__main__':
    for n in (2,3):
        a=checker(n);print(n,'states: components / nonsynchronizing / min-images / continuation tests =',*a)
    print('Advertisement tests finding a marker / crossing from an earlier component:',*markers())
    overlapping();phase_example()
