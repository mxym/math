#!/usr/bin/env python3
"""Synthetic checks for phase projection, smooth cutoff, and a stopped ratio."""
from cmath import exp as cexp
from fractions import Fraction as F
from itertools import product
from math import cos, erfc, exp, pi, sqrt
from random import Random

def law(xs):
    return tuple(F(x,sum(xs)) for x in xs)

# Exact adaptive trees test the reference-path conditional chi-square sum.
rng=Random(15)
trees=leaves=with_cross=0
for t in range(160):
    n=3+t%3
    depth=3+t%2
    probs={}
    for k in range(depth):
        for path in product(range(n),repeat=k):
            qs=law([rng.randrange(1,30) for _ in range(n)])
            ps=law([rng.randrange(0,30) for _ in range(n-1)]+[1+rng.randrange(29)])
            if t%2:
                e=F(1,30)
                ps=tuple((1-e)*q+e*p for q,p in zip(qs,ps))
            probs[path]=qs,ps
    D=F(0); Q=[]; P=[]; S=[]; cross=[]
    def walk(path,q,p,s,crossed):
        global D
        if len(path)==depth:
            Q.append(q); P.append(p); S.append(s); cross.append(crossed)
            return
        qs,ps=probs[path]
        D+=q*sum((a-b)**2/a for a,b in zip(qs,ps))
        for j,(a,b) in enumerate(zip(qs,ps)):
            qq=q*a
            ss=s*(a if crossed else b)
            R=ss/qq
            walk(path+(j,),qq,p*b,ss,crossed or R<F(1,2) or R>2)
    walk((),F(1),F(1),F(1),False)
    assert sum(Q)==sum(P)==sum(S)==1
    var=sum((s-q)**2/q for q,s in zip(Q,S))
    assert var<=4*D
    qc=sum(q for q,e in zip(Q,cross) if e)
    pc=sum(p for p,e in zip(P,cross) if e)
    sc=sum(s for s,e in zip(S,cross) if e)
    assert pc==sc and qc<=16*D and sc<=24*D
    assert sum(abs(p-s) for p,s in zip(P,S))/2<=24*D
    assert all(p==s or e for p,s,e in zip(P,S,cross))
    trees+=1; leaves+=len(Q); with_cross+=qc>0

# Exact ternary Fourier masses of a positive symmetric capped grid toy.
q=3; m=4
grid=list(product(range(q),repeat=m))
L={s:F(2)**sum(a==0 for a in s)*F(1,2)**sum(a!=0 for a in s) for s in grid}
assert sum(L.values())==len(grid)
def masses(A):
    out={}
    for w in grid:
        e=[sum((A[s] for s in grid if sum(x*y for x,y in zip(s,w))%3==r),F(0))/len(grid)
           for r in range(3)]
        a,b=e[0]-e[2],e[1]-e[2]
        out[w]=a*a-a*b+b*b
    assert sum(out.values())==sum(a*a for a in A.values())/len(grid)
    return out
powers=0
for c in (F(1),F(3,2),F(2),F(5,2),F(3)):
    U={s:min(c,L[s]) for s in grid}
    masses_u=masses(U)
    for k in range(17):
        u=F(k,16)
        aq=sum(u**(2*sum(a!=0 for a in s))*w for s,w in masses_u.items())
        assert aq<=(1+u*u/2)**m
        powers+=1
    for s in grid:
        r=sum(a!=0 for a in s)
        for t in grid:
            if sum(a!=0 for a in t)==r:
                assert masses_u[s]==masses_u[t]

# Floating diagnostics for the elementary Fourier and uniform phase formulas.
fourier=phase=0
for d in (1,2,6,12):
    for x in (.4,1.7):
        for sig in (.25,.65):
            a=x*d; sd=sig*sqrt(d); norm=exp(a+sd*sd/2)
            lo=min(-26,a-20); hi=a+18*sd+10
            N=5000; step=(hi-lo)/N
            for xi in (0,.2,.65,1.1,2.3,4):
                integral=0j
                for j in range(N+1):
                    u=lo+j*step
                    v=exp(u)*.5*erfc((u-a)/sd/sqrt(2))/norm
                    integral+=((.5 if j in (0,N) else 1)*v)*cexp(-1j*xi*u)
                s=1-1j*xi
                expect=cexp(s*a+s*s*sd*sd/2)/(s*norm)
                assert abs(integral*step-expect)<2e-8
                fourier+=1
for q in (3,5,7,9,11):
    for j in range(31):
        eta=j/31
        cs=[cos(2*pi*(i+eta)/q) for i in range(q)]
        assert abs(sum(cs))<1e-12 and abs(sum(c*c for c in cs)/q-.5)<1e-12
        phase+=1
print("PASS stopped trees/leaves/crossing / positive sector powers / cutoff Fourier / uniform phases:",
      trees,leaves,with_cross,powers,fourier,phase)
