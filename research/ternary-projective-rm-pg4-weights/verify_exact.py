#!/usr/bin/env python3
"""Integer-only comparison of the published formulas and moment certificates."""
from functools import lru_cache
from hashlib import sha256
from itertools import product
import sys


def P(m):
    return (3**(m+1)-1)//2


def ds(i):
    s = 0
    while i:
        i, r = divmod(i,3)
        s += r
    return s


@lru_cache(None)
def count(n,t):
    return sum(ds(i)<=t for i in range(n))


@lru_cache(None)
def k(m,d):
    return sum(count(3**j,d-1) for j in range(m+1))


@lru_cache(None)
def h(n,d):
    if n==0 or d<=0:
        return 0
    s = 0
    while 3**(s+1)<=n:
        s += 1
    a,b = divmod(n,3**s)
    if b<=P(s-1):
        return count(a*3**s,d)+h(b,d-2)
    return min(count(n,d),k(s,d)+count(n-P(s),d-1))


@lru_cache(None)
def upper(m,d):
    p = P(m)
    kd = k(m,d)
    by_rank = [0]*(kd+1)
    for n in range(1,p+1):
        i = h(n,d)
        assert 0 <= i <= kd
        by_rank[i] = n
    for i in range(1,kd+1):
        by_rank[i] = max(by_rank[i], by_rank[i-1])
    return (0,) + tuple(p-by_rank[kd-r] for r in range(1,kd+1))


@lru_cache(None)
def affine(m,d):
    n = 3**m
    return (0,)+tuple(n-z for z in reversed(range(n)) if ds(z)<=d)


def known(m,d):
    if d<=0:
        return (0,)
    if d<=2:
        w=[0]
        offset=0
        for j in reversed(range(m+1)):
            w.extend(offset+a for a in affine(j,d-1)[1:])
            offset += 3**j
        return tuple(w)
    if d==2*m-1:
        excluded={P(m)+1-b for b in known(m,1)[1:]}
        return (0,)+tuple(v for v in range(1,P(m)+1) if v not in excluded)
    if d==2*m:
        return (0,)+tuple(range(2,P(m)+1))
    if d>2*m:
        return tuple(range(P(m)+1))
    return None


def rank_data(r,L,E,A,B):
    for a,g in product(range(len(L)),range(len(E))):
        if not (0<=g<=a<=r and r-a<len(A) and r-g<len(B)):
            continue
        yield a,g,max(L[a],E[g]),max(A[r-a],B[r-g])


EXPECTED = {
    (3,4,1):(5,((1,0,2,2),)),
    (3,4,7):(15,((4,1,6,6),(5,1,6,6))),
    (4,3,11):(76,((6,0,22,22),(8,0,25,25))),
    (4,6,31):(44,((13,6,14,14),(14,8,17,17),(15,8,17,17),(15,9,18,18),
                   (16,8,17,17),(16,9,18,18),(17,9,18,18))),
}


def moments(m,w,points):
    assert points
    lo,hi = min(points),max(points)
    s1 = w*P(m-1)
    s2 = s1+w*(w-1)*P(m-2)
    return (s1 < P(m)*lo or s1 > P(m)*hi or
            s2 > (lo+hi)*s1-lo*hi*P(m))


def main():
    b3=known(2,3)
    assert b3==(0,3,4,6,7,8,9,10,11,12,13)
    assert known(2,2)==(0,6,8,9,11,12,13)
    profiles={}
    log={}
    for m in (2,3,4):
        for d in range(1,2*m+2):
            ans=upper(m,d)
            base=known(m,d)
            if base is not None:
                assert ans==base
            else:
                L=profiles[m-1,d]
                E=profiles[m-1,d-2]
                A=affine(m,d-1)
                B=affine(m,d)
                gaps=[]
                direct=[]
                for r,w in enumerate(ans[1:],1):
                    tuples=list(rank_data(r,L,E,A,B))
                    lb=min(l+u for a,g,l,u in tuples)
                    assert lb<=w
                    if lb<w:
                        direct.append(r)
                    nh=P(m-1)
                    after=min(max(l+u,(l*P(m)+nh-1)//nh) for a,g,l,u in tuples)
                    assert lb<=after<=w
                    if (m,d,r) in EXPECTED:
                        assert lb+1==w
                        survivors=tuple((a,g,l,lb-u) for a,g,l,u in tuples if l+u<=lb)
                        assert EXPECTED[m,d,r]==(lb,survivors)
                        assert moments(m,lb,{x for _,_,a,b in survivors for x in range(a,b+1)})
                        log[m,d,r]=(lb,w,survivors)
                    if after<w:
                        assert (m,d,r) in EXPECTED and after==lb
                        gaps.append(r)
                assert direct=={(3,4):[1,7],(4,3):[11],(4,4):[1,2,5,11,12,15,21,32,38],
                                (4,5):[21],(4,6):[1,7,31,32]}.get((m,d),[])
                assert gaps=={(4,3):[11],(4,6):[31]}.get((m,d),[])
                print(f"Formula comparison m={m}, d={d}: {len(ans)-1} weights, raw gaps={direct}, least-intersection gaps={gaps}")
            assert all(i<j for i,j in zip(ans,ans[1:]))
            profiles[m,d]=ans
    assert set(log)==set(EXPECTED)
    for m,d,r in sorted(log):
        lo,hi,s=log[m,d,r]
        print(f"Incidence exclusion m={m},d={d},r={r}: {lo}->{hi}; rank/interval tuples {s}")
    for a,b in ((1,7),(3,5)):
        excluded={122-w for w in profiles[4,a][1:]}
        assert tuple(i for i in range(1,122) if i not in excluded)==profiles[4,b][1:]
    assert not moments(4,44,set(range(0,41)))  # No contradiction without restrictions.
    print("Dimension-4 profile dimensions by degree:",
          [len(profiles[4,d])-1 for d in range(1,10)])
    canonical=repr(tuple(profiles[4,d] for d in range(1,10))).encode()
    print("Dimension-4 profile SHA256:",sha256(canonical).hexdigest())
    if sys.argv[1:]==["--tables"]:
        for d in range(1,10):
            print(f"d={d}:", *profiles[4,d][1:])


if __name__=="__main__":
    main()
