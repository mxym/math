#!/usr/bin/env python3
from random import Random

def count_rank(words):
    residues=list(words)
    ans=0
    while any(residues):
        p=max(residues)
        ans+=1
        h=1<<(p.bit_length()-1)
        residues=[(w^p) if (w&h) else w for w in residues]
    return ans

def evaluate_anf(C):
    f=C[:]
    k=len(f).bit_length()-1
    for j in range(k):
        u=1<<j
        for v in range(1<<k):
            if v&u:
                f[v]^=f[v^u]
    return f

def independent_check(k,C):
    full=(1<<k)-1
    T=C[full]
    assert T
    upper=[C[full^(1<<j)] for j in range(k)]
    b=k+1-count_rank([T,*upper])
    f=evaluate_anf(C)
    Z=[]
    for ell in range(1,1<<k):
        moments=[0,0]
        for i,val in enumerate(f):
            moments[(ell&i).bit_count()&1]^=val
        assert moments[0]^moments[1]==T
        if moments[0]==0:
            Z.append((ell,0))
        if moments[1]==0:
            Z.append((ell,1))
    assert len(Z)==2**b-1
    E=[v for v in range(1<<k) if all((ell&v).bit_count()%2!=s for ell,s in Z)]
    assert len(E)==1<<(k-b)
    assert {(ell,s) for ell in range(1,1<<k) for s in (0,1)
            if all((ell&v).bit_count()%2!=s for v in E)}==set(Z)
    r=count_rank([x^f[0] for x in f])
    if b==0:
        assert r>=k+1
    return b

rng=Random(3562609)
counts=set()
for k in range(2,8):
    for _ in range(100):
        m=rng.randrange(1,k+3)
        C=[rng.randrange(1<<m) for _ in range(1<<k)]
        C[-1]=rng.randrange(1,1<<m)
        counts.add(independent_check(k,C))
assert counts==set(range(8))
print("independent ANF/XOR moment path: 600 exact tests over k=2..7, kernel dimensions 0..7 PASS")
