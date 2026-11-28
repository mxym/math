#!/usr/bin/env python3
"""Finite identities for the correlated torus proof; no ring-search experiments."""
from fractions import Fraction as F
from itertools import product
from random import Random

rng=Random(917)
def shift(x):
    return (-x[-1],)+x[:-1]
def norm2(x): return sum(a*a for a in x)
def energy(x,r):
    return norm2(x)+2*r*sum(a*b for a,b in zip(x,shift(x)))
def components(x):
    d=len(x)
    if all(x): return [tuple(range(d))]
    ans=[]
    for j in range(d):
        if x[j] and not x[(j-1)%d]:
            c=[]; h=j
            while x[h]:
                c.append(h); h=(h+1)%d
            ans.append(tuple(c))
    return ans

energies=shells=0
for d in (4,8):
    for rho in (F(1,6),F(1,3),F(3,8),F(7,16)):
        delta=1-2*rho
        dip=0
        vectors=list(product((-1,0,1),repeat=d))
        vectors += [tuple(rng.randrange(-3,4) for _ in range(d)) for i in range(180)]
        for j,x in enumerate(vectors):
            E=energy(x,rho)
            assert E==delta*norm2(x)+rho*norm2(a+b for a,b in zip(x,shift(x)))
            assert E>=delta*norm2(x)
            comps=components(x)
            assert sum(len(C) for C in comps)==sum(bool(a) for a in x)
            es=[]
            for C in comps:
                v=tuple(x[i] if i in C else 0 for i in range(d))
                e=energy(v,rho); es.append(e)
                if len(C)==1:
                    assert e==norm2(v)
                if len(C)<d:
                    assert e>=delta*norm2(v)+2*rho
                if len(comps)==1 and len(C)==2:
                    if e==1+delta:
                        assert norm2(v)==2
                        if j<3**d: dip+=1
                    elif norm2(v)==2:
                        assert e==2+2*rho
                    else:
                        assert e>=1+4*delta
            assert E==sum(es)
            energies+=1
        assert dip==2*d
        shells+=1

pairs=conditional_cov=0
# A positive finite law over a cyclic grid with a translation subgroup.
# The score can be an arbitrary rational test of the original error.
for q,m in product((3,5,9),(2,4,7)):
    n=q*m
    for _ in range(17):
        w=[rng.randrange(1,29) for j in range(n)]
        f=[F(n*v,sum(w)) for v in w]
        g=[sum(f[j+k*m] for k in range(q))/q for j in range(m)]
        s=[F(rng.randrange(-15,17),rng.randrange(1,9)) for j in range(n)]
        marg=[F(0)]*n
        total=prodscore=F(0)
        for a,b in product(range(n),repeat=2):
            if a%m!=b%m: continue
            gu=g[a%m]
            r=gu/F(n*q)*(f[a]/gu)*(f[b]/gu)
            ma=gu/m
            split=ma*f[a]/(q*gu)*f[b]/(q*gu)
            assert r==split
            total+=r; marg[a]+=r
            prodscore+=r*s[a]*s[b]
            pairs+=1
        assert total==1 and marg==[x/n for x in f]
        mean1=sum(s[i]*marg[i] for i in range(n))
        mean_c=[sum(f[j+k*m]*s[j+k*m] for k in range(q))/(q*g[j]) for j in range(m)]
        assert prodscore-mean1*mean1==sum(g[j]/m*(mean_c[j]-mean1)**2 for j in range(m))
        conditional_cov+=1

print("PASS energy decomposition / edge shells / exact grid tilt pairs / conditional covariance:",
      energies,shells,pairs,conditional_cov)
