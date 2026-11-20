"""Verify an exact positive certificate without a table of graphs, an LP solver, or floating point."""
from itertools import combinations, permutations, product
from functools import lru_cache
from collections import Counter
from fractions import Fraction as F
import math

if not __debug__:
    raise RuntimeError('Run without Python optimization so all exact assertions are checked.')

CERT=[(7,0x7cf0c,'1/2'),(8,0x1f996a0,'421/2340'),(9,0xf67e0000,'1/104'),
(9,0xf67e1a00,'7/90'),(9,0x1757e04a0,'1/13'),(9,0x1757e44a0,'29/1170'),
(9,0x1b5bb2b00,'1/13'),(9,0x2b6af1a00,'119/2340'),(9,0x4baa65a00,'17/1170'),
(9,0x4bcb16300,'61/1170'),(9,0x8ea5c2500,'17/1170'),(9,0xa63475200,'1/39'),
(9,0xc34b53380,'7/585')]
TARGET=(6,0x5674)
def decode(n,word):
    rows=[0]*n
    for j in range(1,n):
        for i in range(j):
            if word>>(j*(j-1)//2+i)&1:rows[i]|=1<<j;rows[j]|=1<<i
    return tuple(rows)
def edges(a):return [(i,j) for j in range(len(a)) for i in range(j) if a[i]>>j&1]
def add(a,i,j):
    a=list(a);a[i]|=1<<j;a[j]|=1<<i;return tuple(a)
def ok(a):
    return all((a[i]&a[j]).bit_count()+(a[i]>>j&1)<=2 for i,j in combinations(range(len(a)),2))
def bits(a):return sum(1<<(j*(j-1)//2+i) for i,j in edges(a))
@lru_cache(None)
def canon(a):
    # Equitable color refinement orders distinguishable vertex classes. Then
    # literally try all permutations within the terminal classes, not a graph database.
    n=len(a);colors=(0,)*n
    while True:
        keys=[(colors[i],tuple(sum((a[i]>>j)&1 for j in range(n) if colors[j]==c)
                            for c in range(max(colors)+1))) for i in range(n)]
        labels={z:j for j,z in enumerate(sorted(set(keys)))}; cc=tuple(labels[z] for z in keys)
        if cc==colors:break
        colors=cc
    groups=[tuple(i for i in range(n)if colors[i]==j)for j in range(max(colors)+1)]
    best=None
    for perms in product(*(permutations(c)for c in groups)):
        p=sum(perms,());z=sum(((a[p[i]]>>p[j])&1)<<(j*(j-1)//2+i) for j in range(n)for i in range(j))
        if best is None or z<best:best=z
    return n,best
def plus(out,src,s):
    for k,t in src.items():
        out[k]+=s*t
        if not out[k]:del out[k]
@lru_cache(None)
def inj(key):
    a=decode(*key);n=len(a)
    if n==1:return Counter({(0,0):99})
    x=min(range(n),key=lambda v:a[v].bit_count());d=a[x].bit_count()
    if d>=3:return Counter({key:1})
    rem=[j for j in range(n)if j!=x]
    h=tuple(sum((a[i]>>j&1)<<jj for jj,j in enumerate(rem)) for i in rem)
    S=[ii for ii,j in enumerate(rem)if a[x]>>j&1];out=Counter()
    def term(w,t):
        if ok(w):plus(out,inj(canon(w)),t)
    term(h,(100-n,14,2)[d])
    if d==2:term(add(h,*S),-1)
    if d:
        for v in range(n-1):
            if v in S:continue
            w=h
            for j in S:w=add(w,j,v)
            term(w,-1)
    return out
def induced(n,mask):
    h=decode(n,mask);assert ok(h);extra=[(i,j)for i,j in combinations(range(n),2)if not (h[i]>>j&1)]
    tally=Counter();vis=0
    def dfs(a,start,sign):
        nonlocal vis;vis+=1;plus(tally,inj(canon(a)),sign)
        for k in range(start,len(extra)):
            b=add(a,*extra[k])
            if ok(b):dfs(b,k+1,-sign)
    dfs(h,0,1)
    return tally,vis
def is_N3(a):
    n=len(a);tri=[t for t in combinations(range(n),3) if all(a[i]>>j&1 for i,j in combinations(t,2))]
    return len(tri)==2 and not set(tri[0])&set(tri[1]) and sum(a[i]>>j&1 for i in tri[0]for j in tri[1])==2
def main():
    a=decode(*TARGET);assert is_N3(a)
    aut=sum(all((a[i]>>j&1)==(a[p[i]]>>p[j]&1)for i,j in combinations(range(6),2))for p in permutations(range(6)));assert aut==4
    out,vis=induced(*TARGET);ns=[vis]
    for n,m,value in CERT:
        q=F(value);assert q>0
        data,vis=induced(n,m);ns.append(vis);plus(out,data,-q)
    assert dict(out)=={(0,0):F(83160,13)},out
    print('14 induced templates: admissible labeled supersets tested',ns)
    print('Full exact cancellation leaves 83160/13; target automorphisms =',aut)
    print('n3 >= 20790/13. Since 3 divides n3, n3 >= 1602. PASS')
if __name__=='__main__':main()
