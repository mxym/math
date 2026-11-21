"""Exact profile exponents and nonzero phase injection in BalancedLargeTagTaper."""
from fractions import Fraction as F
from itertools import product
from math import gcd

def need(ok, label):
    if not ok:
        raise RuntimeError(label)

# Monotone linear rails: alpha upper varies with sigma, finite corners suffice.
diag_max=F(0)
off_max=F(0)
for sigma, lam, b, d, e, g in product(
        (F(".10"),F(".14")),
        (F("-.11"),F(".010")),
        (F(".300"),F(".506")),
        (0,F(".001")),
        (0,F(".001")),
        (0,F(".0001"))):
    a=(1-sigma)/2+lam
    z=F(".0002")
    t=a+b+sigma+d+e+g-1+z
    need(t-sigma <= F("-.0317"), "frequency is strictly below small prime")
    need(sigma+t-b < F("-.25"), "no wrap modulo the big prime")
    if t<0:
        continue
    need(b>=F(".4177") and a<3*b/2, "complete-period cost")
    diag=1-sigma-a-g+a+(sigma+t)/2
    off=1-sigma-a-g+a/2+(sigma+t)+b/4+e/2
    need(diag==1+(a+b+d+e-1-g+z)/2, "summed diagonal")
    need(off==a/2+sigma+5*b/4+d+3*e/2+z, "summed off-diagonal")
    diag_max=max(diag_max,diag)
    off_max=max(off_max,off)

need(diag_max<=F(".9841") and off_max<=F(".9952"), "strict power reserve")
need(F(".4")*(1-F(".14"))>F(".340"), "q mark lower endpoint")
need(F(".31")>F(".300") and F(".506")>F(".5"), "m mark endpoints")
need(F(".4")*F(".31")==F(".124"), "literal physical taper")
need(F(".1225")+F(".44425")+F(".43325")==1, "actual q semiprime profile")
need(F(".503")+F(".497")==1, "actual m semiprime profile")
need(F(".001")<F(".44425")-(1-F(".1225"))/2<F(".010"), "unique q mark")

def prime(m):
    return m>=2 and all(m%k for k in range(2,int(m**.5)+1))
pcases=0
S=(11,13,17)
T=9
for r in range(2*max(S)*T+1,550):
    if not prime(r):
        continue
    ratios={}
    for s,k in product(S,range(-T,T+1)):
        if k==0:
            continue
        u=k*pow(s,-1,r)%r
        need(u not in ratios,"exact phase injectivity")
        ratios[u]=(s,k)
    pcases+=len(ratios)
    for e in (1,2,5,10,21):
        P=r*e
        for c in (2,3,5,7,14,21,35):
            if r%c==0 or c%r==0:
                continue
            need(gcd(c,P)<=e, "possible lost coprimality paid by e")
print("Maximum exponents:",float(diag_max),float(off_max),";",pcases,"injective phase samples")
