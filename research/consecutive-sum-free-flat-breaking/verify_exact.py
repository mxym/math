#!/usr/bin/env python3
from functools import reduce
from itertools import product
from operator import xor

def vector_sum(words):
    return reduce(xor,words,0)

def spans(words):
    S={0}
    for w in words:
        if w not in S:
            S.update((u^w) for u in tuple(S))
    return S

def partition(k):
    H=[]
    for ell in range(1,1<<k):
        S=frozenset(v for v in range(1<<k) if (ell&v).bit_count()%2)
        H.append((S,frozenset(range(1<<k))-S))
    return H

def inspect(k,f,H):
    T=vector_sum(f)
    if not T:
        return None
    p=len(f)
    W=spans(w^f[0] for w in f)
    r=len(W).bit_length()-1
    common=frozenset(range(p))
    zeroes=[]
    for pair in H:
        s,t=(vector_sum(f[v] for v in X) for X in pair)
        assert s^t==T and (s or t)
        if not s:
            zeroes.append(pair[0])
            common &= pair[1]
        if not t:
            zeroes.append(pair[1])
            common &= pair[0]
    z=len(zeroes)
    assert (z+1)&z==0 and len(common)*(z+1)==p
    assert {X for pair in H for X in pair if not X&common}==set(zeroes)
    assert z>=2**max(0,k-r+1)-1
    if not z:
        assert r>=k+1 and len(set(f))<len(W)
    if len(set(f))==len(W):
        assert r<k and z>=3
    return z,r

for k,m in ((2,3),(3,2)):
    H=partition(k)
    checked=no_zero=flat=0
    for f in product(range(1<<m),repeat=1<<k):
        obs=inspect(k,f,H)
        if obs is not None:
            z,r=obs
            checked+=1
            no_zero+=z==0
            flat+=len(set(f))==1<<r
    print(f"all maps k={k},m={m}: {checked} nonzero totals; {no_zero} all hyperplane sums nonzero; {flat} flat images")

examples=0
for k in range(2,10):
    H=partition(k)
    for r in range(1,k):
        f=[x&((1<<r)-1) for x in range(1<<k)]
        f[0]^=(1<<r)-1
        for i in range(r-1):
            f[1<<i]^=1<<i
        assert set(f)==set(range(1<<r))
        assert inspect(k,f,H)==((1<<(k-r+1))-1,r)
        examples+=1
    f=[0]*(1<<k)
    f[0]=(1<<(k+1))-1
    for i in range(k):
        f[1<<i]=1<<(i+1)
    assert inspect(k,f,H)==(0,k+1)
print(f"local attainment: {examples} surjective flat-image counts, 8 minimal full-span examples PASS")
assert inspect(3,[0]*8,partition(3)) is None
print("zero-total negative control: 14 zero-sum hyperplanes, excluded from exact-count theorem")
