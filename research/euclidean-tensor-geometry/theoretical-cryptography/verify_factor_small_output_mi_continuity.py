
"""Exact arithmetic examples for fixed-prior continuity thresholds."""
from fractions import Fraction as F
from itertools import product, combinations
from math import prod
from random import Random

def sums(weights, f, b):
    return tuple(sum(w for w,k in zip(weights,f) if k==j) for j in range(b))

def ent_inverse(weights):
    # For a fixed total integer mass, a larger entropy has a smaller product.
    return prod(a**a for a in weights if a)

def boundary(prior,b):
    parts=sorted(set(sums(prior, f, b) for f in product(range(b),repeat=len(prior))))
    n=sum(prior)
    i=min(ent_inverse(p) for p in parts)
    f=F((b-1)*max(map(min,parts)),n)
    a=1-F(max(max(p) for p in parts if ent_inverse(p)==i),n)
    return f,a,parts

def fano_reverse(p,delta):
    b=len(p)
    z=delta/(b-1)
    v=tuple((x-z)/(1-delta-z) for x in p)
    assert all(x>=0 for x in v) and sum(v)==1
    tab=[[v[j]*(1-delta if i==j else z) for j in range(b)] for i in range(b)]
    assert tuple(map(sum,tab))==tuple(p)
    assert sum(tab[i][j] for i in range(b) for j in range(b) if i!=j)==delta
    for j in range(b):
        if v[j]>0:
            assert tab[j][j]/v[j]==1-delta
            assert all(tab[i][j]/v[j]==z for i in range(b) if i!=j)

def main():
    rng=Random(9501)
    counts=[0,0,0,0]
    for s in range(2,7):
      for _ in range(44):
        prior=tuple(rng.randrange(1,13) for i in range(s))
        n=sum(prior)
        for b in range(2,min(4,s+1)+1):
            u,v,parts=boundary(prior,b)
            assert 0<=u<=v<=1-F(1,b)
            counts[0]+=1
            if b==2:
                beta=F(max(map(min,parts)),n)
                assert u==v==beta
                for j in range(1,11):
                    d=j*beta*(1-beta)/5
                    p=(beta,1-beta)
                    t=((p[0]-d/2,d/2),(d/2,p[1]-d/2))
                    assert tuple(map(sum,t))==p and tuple(map(sum,zip(*t)))==p
                    assert t[0][1]+t[1][0]==d
                    counts[1]+=1
            p=tuple(F(x,n) for x in max(parts,key=min))
            for j in range(1,8):
                if u>0:
                    fano_reverse(p,j*u/8)
                    counts[2]+=1
    for b in range(2,13):
      for _ in range(100):
        P=sorted(rng.randrange(1,25) for _ in range(b+1))
        base=sorted(P[2:]+[P[0]+P[1]],reverse=True)
        for i,j in combinations(range(b+1),2):
            p=sorted([P[k] for k in range(b+1) if k not in (i,j)]+[P[i]+P[j]],reverse=True)
            assert all(sum(base[:k])<=sum(p[:k]) for k in range(1,b+1))
            counts[3]+=1
    print("PASS rational partitions, equal-marginal toggles, reverse Fano, majorization",counts,sum(counts))

if __name__=="__main__":
    if not __debug__: raise RuntimeError("run without python -O")
    main()
