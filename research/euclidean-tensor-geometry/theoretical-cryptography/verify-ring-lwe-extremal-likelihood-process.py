#!/usr/bin/env python3
"""Synthetic checks for the transform and constants of the extremal likelihood theorem."""
from cmath import exp as cexp, log as clog
from itertools import product
from math import cos, exp, log, pi, sqrt
from random import Random

def mul(a,b,q):
    d=len(a)
    r=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r[(i+j)%d] += x*y*(-1 if i+j>=d else 1)
    return tuple(x%q for x in r)

def transforms(q,d,b,experiments):
    # Circle quadrature with independent residuals, shared finite uniform design.
    # The explicit analytic remainder is proved in the text, not by quadrature.
    N=56
    f=lambda y: 1+2*sum(b**(h*h)*cos(2*pi*h*y) for h in range(1,5))
    y=[j/N for j in range(N)]
    g=[sum(f(x-u/q) for u in range(q))/q for x in y]
    ell=[[log(f(x-u/q)/gx) for x,gx in zip(y,g)] for u in range(q)]
    vals=[]
    C=0j
    for labels, exponents in experiments:
        C+=sum(a*(a-1) for a in exponents)
        arr={}
        for shifts in product(range(q),repeat=len(labels)):
            arr[shifts]=sum(g[j]*cexp(sum(a*ell[u][j]
                         for a,u in zip(exponents,shifts))) for j in range(N))/N
        vals.append((labels,arr))
    ar=[];total=0j
    for A in product(range(q),repeat=d):
        value=1
        for labels,arr in vals:
            images=[mul(A,L,q) for L in labels]
            for j in range(d):
                value*=arr[tuple(img[j] for img in images)]
        ar.append(value)
        total+=value
    pred=d*b*b*C
    err=abs(clog(total/(q**d))-pred)
    assert err<=60*d*b**4, (q,d,b,err/(d*b**4))
    return len(ar)

test_rows=0
for q,d in [(3,2),(3,4),(5,2)]:
    s=(0,)*d
    a=(1,)+(0,)*(d-1)
    c=(0,1)+(0,)*(d-2)
    if q==3 and d==4: # x^2+x+2 belongs to a proper CRT factor.
        c=(2,1,1,0)
    for b in (.12,.08,.04,.02):
        ex=[((s,a,c),(1.22+.2j,.7-.4j,1.11+.35j)),
            ((s,c,a),(.81-.35j,.5+.25j,1.28-.2j))]
        test_rows+=transforms(q,d,b,ex)
        test_rows+=transforms(q,d,b,ex[:1])
        test_rows+=transforms(q,d,b,[((s,a),(1.32j+1,.93-.22j))])

coh=0
for q,d in [(3,4),(5,2),(9,2)]:
    universe=list(product(range(q),repeat=d))
    for diff in universe[1:]:
        images=[mul(a,diff,q) for a in universe]
        xs=[[cos(2*pi*a[j]/q) for a in images] for j in range(d)]
        eps=1e-11
        for i in range(d):
            assert abs(sum(xs[i]))<eps
            assert abs(sum(x*x for x in xs[i])/len(images)-.5)<eps
            for j in range(i):
                assert abs(sum(x*y for x,y in zip(xs[i],xs[j])))<eps
                coh+=1

# Gaussian comparison evaluated with the logarithmic centering.
e=0
for B,t in [(.4,.6),(.75,.75),(1.0,.7),(1.4,2.2)]:
    a=sqrt(B/t)
    for d in (2**14,2**17,2**20):
        logn=B*d; V=2*t*d
        z=sqrt(2*logn)-(log(logn)+log(4*pi))/(2*sqrt(2*logn))
        ld=z/sqrt(V)
        lin=logn-z*z/2-.5*log(2*pi*V)
        assert abs(exp(lin)/a-1)<.004
        for x in (-4,-1,0,2,4):
            p=exp(lin-ld*x-x*x/(2*V))
            assert abs(p/(a*exp(-a*x))-1)<.01
            for u in (-1.7,.1,1.4):
                # Product with the limiting local true Gaussian density factor.
                v=u*sqrt(V)+x
                p_true=exp(-v*v/(2*V))/sqrt(2*pi)
                phi=exp(-u*u/2)/sqrt(2*pi)
                assert abs(p_true/phi-1)<.06
                e+=1

rng=Random(172)
N=24000
gaps=[log((x+rng.expovariate(1))/x) for x in (rng.expovariate(1) for _ in range(N))]
gap_results=0
for a in (.4,1,2):
    for y in (.2,.5,1.1,2.2):
        got=sum(g/a>y for g in gaps)/N
        assert abs(got-exp(-a*y))<.015
        gap_results+=1

print("PASS shared-design rows / coefficient cross moments / local Gaussian factors / gap cases:",
      test_rows,coh,e,gap_results)
