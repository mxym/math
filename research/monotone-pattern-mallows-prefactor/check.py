"""Finite checks, not a proof. Python 3 stdlib. Safe with -O."""
from itertools import product, permutations
from fractions import Fraction as Q
from collections import defaultdict
from math import prod, exp, log, cosh, tanh, sqrt, pi
import sys

def eq(a,b):
    if a!=b: raise ValueError((a,b))
def closest(a,b,tol):
    if abs(a-b)>tol: raise ValueError((a,b,tol))

def encode(p):
    h=[]
    for i,x in enumerate(p):
        h.append(1+max((h[j] for j in range(i) if p[j]>x),default=0))
    return tuple(h),tuple(c for _,c in sorted(zip(p,h)))
def reverse(w):return w[::-1]
def tests(u,v,d):
    for i in range(1,d):
        def pre(w):
            a=0; z=[]
            for b in w:
                if b==i:a+=1
                if b==i+1:z.append(a)
            return z
        if any(x<=y for x,y in zip(pre(u),pre(v))):return False
    return True

def poly321(n,q):
    # Signed binary word-pair difference as an area-weighted Motzkin excursion.
    a=[1]
    for k in range(n):
        a=[q**h*((a[h-1] if 0<h<=k+1 else 0)+((1+(h>0))*a[h] if h<=k else 0)
                 +(a[h+1] if h+1<=k else 0)) for h in range(k+2)]
    return a[0]
nchecked=0;good=0
for d,nmax in [(2,8),(3,5),(4,4)]:
    for n in range(1,nmax+1):
        lookup={encode(p):p for p in permutations(range(n)) if max(encode(p)[0])<=d}
        groups=defaultdict(list)
        for u in product(range(1,d+1),repeat=n):
            groups[tuple(u.count(i) for i in range(1,d+1))].append(u)
        hits=0;zs=0
        for ws in groups.values():
            for u,v in product(ws,repeat=2):
                passed=tests(u,v,d);eq(passed,(u,v) in lookup)
                eq(passed,tests(reverse(v),reverse(u),d))
                hits+=passed;nchecked+=1
                if passed and d==2:
                    p=lookup[u,v]; zs+=3**sum(x>y for i,x in enumerate(p) for y in p[i+1:])
        eq(hits,len(lookup));good+=hits
        if d==2:eq(zs,poly321(n,3))
print("equal-content word pairs cross-checked:",nchecked,"; canonical pairs:",good)
print("binary Motzkin weights vs permutations through n=8: PASS")

perms=0;bounds=0;vands=0
for d in range(1,7):
    lam=[2**i for i in range(d)]
    a=[Q(1,l) for l in lam];c=1/sum(a)
    def coef(p):
        sgn=(-1)**sum(x>y for i,x in enumerate(p) for y in p[i+1:])
        return sgn*prod(Q(lam[j],lam[i])**(i+1) for i,j in enumerate(p))
    ps=list(permutations(range(d)));coefs={p:coef(p) for p in ps}
    eq(sum(coefs.values()),prod(1-Q(lam[i],lam[j]) for i in range(d) for j in range(i+1,d)))
    vands+=1
    for yy in [tuple(range(d-1,-1,-1)),tuple(i//2 for i in range(d-1,-1,-1)),(0,)*d]:
        # y_i = yy_i log 2, hence every E_pi and cutoff multiplier here is rational.
        ev={p:Q(2)**sum((lam[i]-lam[j])*yy[i] for i,j in enumerate(p)) for p in ps}
        eq(sum(coefs[p]*ev[p] for p in ps),sum(coefs[p]*ev[p]*sum(
            c/lam[j]*(1 if i==0 else (1-Q(2)**(-lam[j]*(yy[i-1]-yy[i]))))
            for i,j in enumerate(p)) for p in ps))
        for p in ps:
            perms+=1
            for i in range(1,d):
                pp=list(p);pp[i-1],pp[i]=pp[i],pp[i-1];pp=tuple(pp)
                a,b=lam[p[i]],lam[pp[i]];gap=yy[i-1]-yy[i]
                eq(coefs[p]*ev[p]/a*Q(2)**(-a*gap),-coefs[pp]*ev[pp]/b*Q(2)**(-b*gap))
                bounds+=1
print("normalized Vandermondes:",vands,"; kernel terms:",perms,"; boundary partner identities:",bounds)
# A separate floating diagnostic, not an infinite-n certificate.
def logz(n,b):
    qpow=[exp(b*j/n) for j in range(n+1)]
    a=[1.0];ls=0.
    for k in range(n):
        a=[qpow[h]*((a[h-1] if h else 0.)+((1+(h>0))*a[h] if h<=k else 0.)
                    +(a[h+1] if h+1<=k else 0.)) for h in range(k+2)]
        # Only heights that can still reach zero have bearing on the partition function.
        del a[n-k:]
        a.extend([0.]*(k+2-len(a)))
        mx=max(a);ls+=log(mx);a=[e/mx for e in a]
    return ls+log(a[0])
b=4.
# Composite midpoint integral of the smooth d=2 free energy reduction.
f=sum(2*log(2*cosh(b*(k+.5)/(4*10000))) for k in range(10000))/10000
constant=(1-exp(-b/2))**2*sqrt(b/tanh(b/4))/(2*sqrt(pi))
for n in (64,128,256,512):
    ratio=exp(logz(n,b)-n*f+.5*log(n))/constant
    print("beta=4, d=2, n=%3d, exact transfer / leading equivalent = %.8f"%(n,ratio))
print("PASS")
