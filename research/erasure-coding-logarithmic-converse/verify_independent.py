#!/usr/bin/env python3
"""Scalar/trigonometric filter and direct flag-distribution arithmetic."""
from math import atanh,log,exp,cos,acos,acosh,sqrt,floor,ceil,log1p,cosh

def logcosh(x):
    x=abs(x)
    return x+log1p(exp(-2*x))-log(2)

def logabs_cheb(t,y):
    if abs(y)>1:
        return logcosh(t*acosh(abs(y)))
    a=abs(cos(t*acos(y)))
    return log(a) if a>0 else -float("inf")

spectra=far=near=slices=0
for p0 in (.20,.35,.48,.499):
    c0=log((1-p0)/p0); L0=max(3,(log(6)+2)/c0); gamma=min(1,2/sqrt(L0))
    for n in (21,63,255,1024,10000,90000):
        for k in sorted(set(x for x in (floor(p0*n),floor(p0*n/2),2) if 2<=x<=p0*n)):
            for t in sorted(set(x for x in (1,2,3,9,31,k//4,k//2,k-1) if 1<=x<k)):
                L=L0*t
                d=logcosh(t*2*atanh(1/sqrt(L)))
                assert d>=2*sqrt(t/L0)-log(2)-1e-10
                logv=0.
                for j in range(1,k+1):
                    logv+=log((k-j+1)/(n-k-j+1))
                    x=j*(n-j+1)/n
                    y=(L+1-2*x)/(L-1)
                    assert x>=1 and logv<=-c0*x+1e-8
                    lr=logv+logabs_cheb(t,y)-d
                    assert lr<=log(2)-gamma*sqrt(t)+1e-8
                    if x>L:
                        assert lr<=-2*t+1e-8
                        far+=1
                    else:
                        near+=1
                spectra+=1
            slices+=1

tails=capped=equal=under=wide=0
for p in (.07,.25,.45,.49):
    p0=(p+.5)/2; c0=log((1-p0)/p0); L0=max(3,(log(6)+2)/c0)
    c=min(1,2/sqrt(L0))/2
    for n in (97,256,1000,4000):
        mode=floor((n+1)*p)
        pn=[0.]*(n+1); pn[mode]=1.
        for k in range(mode,n):
            pn[k+1]=pn[k]*(n-k)/(k+1)*p/(1-p)
        for k in range(mode,0,-1):
            pn[k-1]=pn[k]*k/(n-k+1)*(1-p)/p
        scale=sum(pn)
        pn=[x/scale for x in pn]
        atom=max(pn)
        ilo=max(2,ceil(n*p/2)); ihi=floor(p0*n)
        exceptional=sum(pn[:ilo])+sum(pn[ihi+1:])
        for d in (2,3,17):
            b=1+log(2*n+7,d)
            for a in (-4*n-.25,-.25,0.,mode-b,mode-.1,float(mode),mode+.25,n+.75):
                below=sum(pn[k] for k in range(n+1) if k<=a)
                total=below+sum(pn[k] for k in range(n+1)
                                 if k>a and (k<ilo or k>ihi))
                bins={}; actual_geom=0.; uncapped=0.; cap=0.
                for k in range(ilo,ihi+1):
                    z=k-a
                    if z==0: equal+=1
                    if z<=0: continue
                    j=floor(z/b)
                    bins[j]=bins.get(j,0)+1
                    if j==0:
                        total+=pn[k]; uncapped+=pn[k]; under+=1
                        continue
                    t=min(j,k-1)
                    exponent=-2*z+b*t
                    assert exponent<=-z+1e-9
                    left=sqrt(min(1,2*exp(-2*c*sqrt(t))+exp(log(d)*exponent)))
                    geo=exp(-log(d)*z/2)
                    env=min(1,sqrt(2)*exp(-c*sqrt(t))+geo)
                    assert left<=env+1e-12
                    total+=pn[k]*left
                    actual_geom+=pn[k]*geo
                    if j>k-1:
                        cap+=pn[k]*sqrt(2)*exp(-c*sqrt(k-1)); capped+=1
                    else:
                        uncapped+=pn[k]*sqrt(2)*exp(-c*sqrt(j)); wide+=1
                assert all(v<=b+1+1e-12 for v in bins.values())
                # Decreasing-series integral bound and a tighter occupied-bin bound.
                binbound=sqrt(2)*atom*(b+1)*sum(exp(-c*sqrt(j)) for j in bins)
                assert uncapped<=binbound+1e-12
                assert actual_geom<=atom/(1-d**(-.5))+1e-12
                assert cap<=sqrt(2)*exp(-c*sqrt(n*p/2-1))+1e-12
                explicit=(below+exceptional+sqrt(2)*atom*(b+1)*(1+2/c**2)
                           +sqrt(2)*exp(-c*sqrt(n*p/2-1))+atom/(1-d**(-.5)))
                assert total<=explicit+1e-12
                tails+=1
assert far and near and capped and equal and under and wide
print("INDEPENDENT PASS:",slices,"slices,",spectra,"spectral sweeps;",
      near,"interior",far,"exterior levels")
print("INDEPENDENT PASS:",tails,"threshold sums;",capped,"capped",equal,"equality",
      under,"short-gap",wide,"uncapped positive-degree counts")
