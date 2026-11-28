#!/usr/bin/env python3
"""ANF orbit folding and full-cycle derivative, using exact bits only."""
from itertools import combinations
from collections import Counter
from random import Random

def orbit(s,n):
    a=[];z=s
    while not a or z!=s:
        a.append(z)
        z=(z>>1)|((z&1)<<(n-1))
    return a

def masks(n,degrees):
    for k in degrees:
        for X in combinations(range(n),k):
            yield sum(1<<i for i in X)

def anf(tt):
    out=tt[:]
    for k in range((len(tt)-1).bit_length()):
        for i in range(len(tt)):
            if i>>k&1:out[i]^=out[i^(1<<k)]
    return out

rand=Random(0x33a5)
total=quartic=quarter=pair=0
for n in (4,12,20,28,36,44):
    seen=set()
    Q=0
    S=list(masks(n,range(1,5)))
    S += list(range(1<<n)) if n==12 else [rand.getrandbits(n) for _ in range(480)]
    for s in S:
        if s in seen or not s:continue
        O=orbit(s,n)
        seen.update(O);d=len(O);even=((1<<n)-1)//3
        B=int(d%4==2 and (s&even==0 or s&(even<<1)==0))
        g=[]
        for u in range(16):
            x=u*((1<<n)-1)//15
            g.append(sum(y&x==y for y in O)%2)
        gA=anf(g)
        assert gA[15]==d%2 and gA[5]==gA[10]==B
        if s.bit_count()==4:
            quartic+=1
            h=n//4
            half=lambda z: ((z>>2*h)|(z<<2*h))&((1<<n)-1)
            turn=lambda z: ((z>>h)|(z<<3*h))&((1<<n)-1)
            short4=int(turn(s)==s); short2=half(s)==s and not short4
            bases=[j for j in range(2*h) if ((s>>j)&1) and ((s>>(j+2*h))&1)]
            two_same=short2 and len(bases)==2 and bases[0]%2==bases[1]%2
            assert gA[15]==short4 and gA[5]==two_same
            if short4:Q+=1;quarter+=1
            if B:assert short2;pair+=1
        total+=1
    assert Q==1

def fold_uv(x):
    b=[(x>>i)&1 for i in range(12)]
    u=tuple((b[i]+b[i+4]+b[i+8])%2 for i in range(4))
    w=[sum(b[j::3])%2 for j in range(3)]
    return u, (w[0]^w[1],w[1]^w[2])

J=(1<<12)-1
F=[]
fib=Counter(fold_uv(x) for x in range(1<<12))
assert len(fib)==64 and all(n==64 for n in fib.values())
for x in range(1<<12):
    (a,b,c,d),v=fold_uv(x)
    F.append(int(not (a or b or c or d)) ^ (((a&c)^(b&d))*int(any(v))))
assert max(i.bit_count() for i,v in enumerate(anf(F)) if v)==4
assert all(F[x]==F[(x>>1)|((x&1)<<11)] for x in range(1<<12))
D=[F[x]^F[x^J] for x in range(1<<12)]
assert sum(D)==2048
assert sum(D[u*0x111] for u in range(16))==2
assert max(i.bit_count() for i,v in enumerate(anf(D)) if v)==3
assert any(y and fold_uv(y)==fold_uv(0) and all(
    F[x]==F[x^y] for x in range(1<<12)) for y in range(1,1<<12))
print("EXACT PASS:",total,"ANF orbits,",quartic,"quartic;",quarter,
      "quarter-turn orbits and",pair,"counted half-turn orbits")
print("EXACT PASS: 4096 fully cyclic inputs, rank-6 fold, derivative weight 2048 vs 2 on the fold")
