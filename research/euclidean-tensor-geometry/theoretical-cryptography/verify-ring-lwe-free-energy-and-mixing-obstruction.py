#!/usr/bin/env python3
"""Synthetic algebra and stationary-flow checks for the proof, not an inference implementation."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from random import Random

rng=Random(81)

def mul(a,b,q):
    d=len(a); c=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            k=i+j
            c[k%d]+=x*y*(-1 if k>=d else 1)
    return tuple(x%q for x in c)

# Uniform nontrivial additive images certify the exact vanishing of the
# primitive character and hence cosine covariance, without floating roots.
marginals=0
for q,d in ((3,2),(5,2),(9,2),(15,2),(3,4),(5,4)):
    R=list(product(range(q),repeat=d))
    gens=R[1:] if len(R)<90 else rng.sample(R[1:],64)
    for g in gens:
        J={mul(g,a,q) for a in R}
        opts=[(j,-1,c) for j in range(d) for c in (1,2)]
        opts += [(j,k,c) for j in range(d) for k in range(j) for c in (-1,1)]
        for j,k,c in opts:
            H=Counter(((c*v[j]) if k<0 else (v[j]+c*v[k]))%q for v in J)
            assert len(H)>1 and len(set(H.values()))==1 and 0 in H
            marginals+=1

# Taylor terms computed with exact Laurent multiplication in the circle
# variable and cyclic phase variable. Exponents themselves are represented
# symbolically through truncated rational binomial expansions.
def add(a,b):
    out=Counter(a)
    for k,v in b.items():
        out[k]+=v
    return {k:v for k,v in out.items() if v}
def poly(a,b,q):
    out=Counter()
    for (h,r,z),u in a.items():
        for (k,s,w),v in b.items():
            if h+k<=3:
                out[(h+k,r+s,(z+w)%q)]+=u*v
    return {k:v for k,v in out.items() if v}
def expand(a,z,q):
    ans={(0,0,0):F(1)}; p=ans
    c={(1,1,-z%q):F(1),(1,-1,z%q):F(1)}
    u=F(1)
    for j in range(1,4):
        u*=F(a-j+1,j)
        p=poly(p,c,q)
        ans=add(ans,{k:u*v for k,v in p.items() if u*v})
    return ans
taylor=0
for q in (3,5,9):
    for _ in range(120):
        m=rng.randrange(2,7)
        av=[F(1)]+[F(rng.randrange(-7,8),rng.randrange(1,6)) for _ in range(m-1)]
        zv=[rng.randrange(q) for _ in range(m)]
        p={(0,0,0):F(1)}
        for a,z in zip(av,zv):
            p=poly(p,expand(a,z,q),q)
        integral={(h,u):v for (h,y,u),v in p.items() if y==0}
        want=Counter({(0,0):F(1),(2,0):sum(a*(a-1) for a in av)})
        for i in range(m):
            for j in range(i):
                for eps in (-1,1):
                    want[(2,eps*(zv[i]-zv[j])%q)]+=av[i]*av[j]
        assert integral=={k:v for k,v in want.items() if v}
        taylor+=1

def energy(t,u,h):
    return (t*(u*u-h+h*h) if h<=u else t*h*(2*u-1))
opt=gap=0
for t in (F(1,3),F(2),F(4,5)):
    for u0 in range(1,26):
        u=F(u0,12)
        for h0 in range(0,33):
            h=F(h0,12)
            fn=lambda x:t*(u*u-x*x+h*(2*x-1))
            exact=max(fn(F(x,12)) for x in range(u0+1))
            assert exact==energy(t,u,h)
            if u==h:
                assert exact==t*h*(2*u-1)
            opt+=1
        for v0 in range(u0+1):
            v=F(v0,12)
            gamma=min(t,energy(t,u,F(1)))-energy(t,v,F(1))
            assert (gamma>0)==(v<min(1,u))
            if v<min(1,u):
                assert gamma==2*t*(min(1,u)-v)
            gap+=1

# Exact stationary-mass tests with asymmetric cycle flux and auxiliary
# states sharing a visible label. These are arbitrary finite probability
# laws and contain no ring-learning inputs, labels or likelihoods.
flowchecks=0
for n in range(4,13):
    for _ in range(24):
        raw=[rng.randrange(1,12) for _ in range(n)]
        p=[F(x,sum(raw)) for x in raw]
        f=[[F(0) for j in range(n)] for i in range(n)]
        for _ in range(n):
            L=rng.sample(range(n),rng.randrange(2,n+1))
            weight=min(p[j] for j in L)/(3*n)
            for i,j in zip(L,L[1:]+L[:1]):
                f[i][j]+=weight
        for i in range(n):
            f[i][i]=p[i]-sum(f[i])
        assert all(sum(f[i][j] for i in range(n))==p[j] for j in range(n))
        marked=set(rng.sample(range(n),rng.randrange(1,n)))
        others=set(range(n))-marked
        nbh={i for i in others if any(f[i][j]>0 for j in marked)}
        fin=sum(f[i][j] for i in others for j in marked)
        fout=sum(f[j][i] for i in others for j in marked)
        assert fin==fout<=sum(p[i] for i in nbh)
        D=marked if sum(p[i] for i in marked)<=F(1,2) else others
        mass=sum(p[i] for i in D)
        v={i:p[i]/mass for i in D}
        for step in range(1,7):
            v={j:sum(v[i]*f[i][j]/p[i] for i in D) for j in D}
            assert 1-sum(v.values())<=step*fin/mass
            flowchecks+=1

print("PASS phase marginals, Taylor rows, free-energy maxima, bottleneck exponents, stationary flow:",
      marginals,taylor,opt,gap,flowchecks)
