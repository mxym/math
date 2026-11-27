#!/usr/bin/env python3
"""Exact finite and analytic profile checks (Python 3 standard library)."""
from fractions import Fraction as F
from itertools import product
from math import erf, exp, log, pi, sqrt


def exact_sandwich(q,m,r):
    Us=tuple(product(range(q),repeat=m))
    outputs=tuple(product(range(q),repeat=r))
    Q=q**r
    H=[F(1,2),F(1,3),F(1,6)]
    P=[F(5,8),F(1,8),F(1,4)]
    sizes=len(Us)
    alpha=[[1]*sizes, [4+((7*i+1)%11) for i in range(sizes)], [1]+[0]*(sizes-1)]
    law=[tuple(F(t,sum(row)) for t in row) for row in alpha]
    cases=(F(1,2),F(1,3),F(1,8))
    counts=0
    for e in cases:
        Good=[[px<=e/Q for px in row] for row in law]
        Bad=[[px>1/(e*Q) for px in row] for row in law]
        Mid=sum(w*sum(px for px,g,b in zip(row,G,B) if not (g or b))
                for w,row,G,B in zip(P,law,Good,Bad))
        Gmass=[sum(px for px,g in zip(row,G) if g) for row,G in zip(law,Good)]
        Clip=sum(max(F(0),h-p*g) for h,p,g in zip(H,P,Gmass))
        Err=F(0)
        for flat in product(range(q),repeat=r*m):
            A=[flat[i*m:(i+1)*m] for i in range(r)]
            images=[tuple(sum(c*b for c,b in zip(row,x))%q for row in A) for x in Us]
            TV=E=F(0)
            support_bad_measure=F(0)
            for h,p,row,G,B,g in zip(H,P,law,Good,Bad,Gmass):
                mass={y:F(0) for y in outputs}
                pg=dict(mass)
                bad_set=set()
                for y,px,good,bad in zip(images,row,G,B):
                    mass[y]+=px
                    if good:
                        pg[y]+=px
                    if bad:
                        bad_set.add(y)
                TV+=sum(max(F(0),h/Q-p*mass[y]) for y in outputs)
                E+=sum(abs(p*pg[y]-p*g/Q) for y in outputs)
                support_bad_measure+=h*F(len(bad_set),Q)
            assert support_bad_measure<=e
            assert Clip-E-Mid-e<=TV<=Clip+E
            Err+=E
            counts+=1
        assert (Err/q**(r*m))**2<=e
    print(f"PASS q={q}, m={m}, r={r}: {counts} exact conditional-hash sandwiches")


def concentrated_bad():
    H=(F(1,4),F(3,4))
    P=(F(3,5),F(2,5))
    for c in (F(1,4),F(3,4),F(5,6)):
        profile=sum(max(F(0),h-c*p) for h,p in zip(H,P))
        base=sum(max(F(0),h-p) for h,p in zip(H,P))
        assert max(base,1-c)<=profile<=base+1-c
        for Q in (3,19,97,127):
            d=sum(sum(max(F(0),h/Q-p*(c/Q+(1-c if j==0 else 0)))
                      for j in range(Q)) for h,p in zip(H,P))
            assert profile-F(1,Q)<=d<=profile
    print("PASS 12 exact clipped comparisons with concentrated bad mass")


def Phi(x):
    return (1+erf(x/sqrt(2)))/2


def closed(v,c):
    if v==0:
        return 1-c
    b=-log(c)
    return Phi((b+v/2)/sqrt(v))-c*Phi((b-v/2)/sqrt(v))


def quad(v,c):
    end=min(10,(-log(c)+v/2)/sqrt(v))
    N=4096
    step=(end+10)/N
    def f(x):
        return max(0.0,1-c*exp(sqrt(v)*x-v/2))*exp(-x*x/2)/sqrt(2*pi)
    return step*(f(-10)+f(end)+sum((4 if i%2 else 2)*f(-10+i*step)
                                   for i in range(1,N)))/3


def verify_profile():
    n=0
    for v,c in product((0.15,0.3,1.0,3.0,12.0),(0.1,0.4,0.75,0.95)):
        d=closed(v,c)
        assert abs(d-quad(v,c))<1e-8
        base=2*Phi(sqrt(v)/2)-1
        assert max(base,1-c)<d<base+1-c
        n+=1
    print(f"PASS {n} Gaussian-integral comparisons and nonadditivity inequalities")


if __name__=="__main__":
    exact_sandwich(2,3,1)
    exact_sandwich(3,2,1)
    exact_sandwich(3,2,2)
    concentrated_bad()
    verify_profile()
