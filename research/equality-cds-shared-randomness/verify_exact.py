#!/usr/bin/env python3
"""Exact full transcript and kernel checks for multi-secret equality CDS."""
from collections import Counter
from fractions import Fraction as F
from itertools import product


def field(d):
    mask = (1 << d) - 1
    poly = {1:3, 2:7, 3:11, 4:19}[d]

    def mul(a,b):
        c = 0
        while b:
            if b&1:
                c ^= a
            b >>= 1
            a <<= 1
            if a >> d:
                a ^= poly
        assert 0 <= c <= mask
        return c

    for a in range(1,1<<d):
        assert len({mul(a,b) for b in range(1<<d)}) == 1<<d
    return mul


def exact_rank(rows):
    A = [list(map(F,row)) for row in rows]
    piv = 0
    for col in range(len(A[0])):
        j = next((j for j in range(piv,len(A)) if A[j][col]),None)
        if j is None:
            continue
        A[piv],A[j] = A[j],A[piv]
        for j in range(piv+1,len(A)):
            if A[j][col]:
                u = A[j][col]/A[piv][col]
                A[j] = [s-u*t for s,t in zip(A[j],A[piv])]
        piv += 1
        if piv == len(A):
            break
    return piv


def run_case(n,ell,split):
    N,M,d = 1<<n,1<<ell,max(n,ell)
    mul = field(d)
    main = list(product(range(1<<d),range(M)))
    atoms = []
    for h,(u,v) in enumerate(main):
        base = F(1,len(main))
        if split:
            ratio = F((h%3)+1,5)
            atoms.extend(((u,v,base*ratio),(u,v,base*(1-ratio))))
        else:
            atoms.append((u,v,base))
    q = len(atoms)
    pi = [r[2] for r in atoms]
    assert sum(pi) == 1

    def mask(x,r):
        u,v,_ = r
        return v ^ (mul(u,x) & (M-1))

    # Extra independent private flags with differently biased local channels.
    # Their distributions depend only on the locally sent masked word.
    def A(x,s,r):
        z = s ^ mask(x,r)
        w = F((z%2)+1,3)
        return (((z,0),w),((z,1),1-w))

    def B(y,r):
        z = mask(y,r)
        w = F((z%3)+1,4)
        return (((z,0),w),((z,1),1-w))

    views = 0
    for x,y in product(range(N),repeat=2):
        target = None
        for s in range(M):
            hist = Counter()
            for r in atoms:
                for (a,pa),(b,pb) in product(A(x,s,r),B(y,r)):
                    hist[a,b] += r[2]*pa*pb
            assert sum(hist.values()) == 1
            if x==y:
                assert all(a[0]^b[0] == s for a,b in hist)
            elif target is None:
                target = hist
            else:
                assert hist == target
            views += 1

    block = []
    for x in range(N):
        # Choose the same actual a=(0,0) independent of the secret.
        vectors = [[pi[j]*dict(A(x,s,r)).get((0,0),0)
                    for j,r in enumerate(atoms)] for s in range(M)]
        masses = {sum(w) for w in vectors}
        assert len(masses)==1 and min(masses)>0
        differences = [[a-b for a,b in zip(w,vectors[0])]
                       for w in vectors[1:]]
        assert all(sum(v)==0 for v in differences)
        for y in range(N):
            images = [[sum(vj*dict(B(y,r)).get((z,b),0)
                           for vj,r in zip(v,atoms))
                       for z,b in product(range(M),(0,1))]
                      for v in differences]
            if y==x:
                assert exact_rank(images)==M-1
            else:
                assert all(not any(v) for v in images)
        block += differences

    rk = exact_rank(block)
    assert rk == N*(M-1) and q >= 1+rk
    # Integer inequalities used to turn the rank and entropy bounds into bits.
    assert 1+rk > (1<<(n+ell-1))
    assert len(main)==(1<<(ell+max(n,ell)))
    assert len(main)>=M*M
    return views,rk


def both_hold_secret_control():
    # Not the modeled protocol: Bob's ability to use s changes the cost.
    for ell in (1,2,3):
        M = 1<<ell
        for x,y in product((0,1),repeat=2):
            laws = []
            for s in range(M):
                h = Counter()
                for u in range(M):
                    a = s^u if x==0 else u
                    b = u if y==0 else s^u
                    assert x!=y or a^b==s
                    h[a,b] += 1
                laws.append(h)
            if x!=y:
                assert all(v==laws[0] for v in laws)
        assert M < max(2*M-1,M*M)


if __name__ == "__main__":
    params = ((1,1,False),(2,1,False),(2,2,False),(3,1,False),
              (1,3,False),(3,2,False),(2,3,False),(3,3,False),
              (2,1,True),(2,2,True),(1,3,True))
    cases = [run_case(*p) for p in params]
    both_hold_secret_control()
    print(f"PASS exact: {len(cases)} multi-secret constructions, {sum(v for v,_ in cases)} full views")
    print(f"PASS exact: direct-sum rank total {sum(r for _,r in cases)}, nonuniform seed splits/private flags, both-hold-secret control")
