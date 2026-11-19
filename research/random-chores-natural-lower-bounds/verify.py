#!/usr/bin/env python3
"""Exact rational enclosures for the constants and a finite-depth margin.
No third-party modules. Floats only format informative, non-proof printouts.
"""
from fractions import Fraction as Q
from functools import lru_cache
N=10**32
def rd(x): return Q((N*x).__floor__(),N)
def ru(x): return Q((N*x).__ceil__(),N)
def check(b):
    if not b: raise AssertionError("certificate failed")
def fmt(r): return '%.13g'%float(r)
@lru_cache(None)
def lnsmall(x):
    check(1<=x<=2)
    y=(x-1)/(x+1); yy=y*y
    term=y;s=Q(0)
    for i in range(40):
        s+=term/(2*i+1); term*=yy
    return rd(2*s),ru(2*(s+term/(81*(1-yy))))
@lru_cache(None)
def ln(x):
    check(x>0); k=0
    while x<1: x*=2;k-=1
    while x>2: x/=2;k+=1
    a,b=lnsmall(x); c,d=lnsmall(Q(2))
    return (a+k*(c if k>=0 else d), b+k*(d if k>=0 else c))
def inclogsum(terms,bias=Q(0)):
    a=b=bias
    for coef,x in terms:
        c,d=ln(x)
        a+=coef*(c if coef>=0 else d);b+=coef*(d if coef>=0 else c)
    return a,b
def Hterms(u,a):
    return [(-a,a),(a-1,1-a),(-a,a/u),(a-u,(u-a)/u),(1+u,(1+u)/(1-a))]
def moment_bounds(u,a):
    j0,j1=inclogsum(Hterms(u,a),-1-u)
    d0,d1=inclogsum([(Q(1),(1-a)*(u-a)/(a*a))],(1+u)/(1-a))
    # Tangent upper bound uses concavity on entire interval [0,u].
    return j0,j1+max(abs(d0),abs(d1))*u
def maximize(u):
    left,right=Q(0),u
    for _ in range(65):
        a=(left+right)/2
        d0,d1=inclogsum([(Q(1),(1-a)*(u-a)/(a*a))],(1+u)/(1-a))
        if d0>0: left=a
        elif d1<0: right=a
        else: break
    return moment_bounds(u,(left+right)/2)
for u,sgn in [('0.26016893448',-1),('0.26016893449',1)]:
    l,h=maximize(Q(u))
    check(h<0 if sgn<0 else l>0)
    print('sup J at u='+u, 'lies in',fmt(l),fmt(h))
# exp(-x) by alternating Taylor, x in [0,3]. Every tail here decreases.
def em(x):
    check(0<=x<=3)
    term=Q(1); s=term
    for i in range(1,65): term=-term*x/i;s+=term
    a=s-term*x/65
    return rd(a),ru(s)
def F_interval(x,typ):
    lo,hi=em(x)
    def form(z):
        g=(2-z) if typ=='two' else (3-z)/(1+z)
        return g
    return (form(hi)*(1+(1+x)*lo)-2*x,
            form(lo)*(1+(1+x)*hi)-2*x)
def critical(typ):
    a,b=Q(1),Q(2)
    for _ in range(70):
        x=(a+b)/2
        el,eh=F_interval(x,typ)
        if el>0:a=x
        elif eh<0:b=x
        else:break
    # c(x)=g(x)/x decreases. g itself increases.
    al,ah=em(a);bl,bh=em(b)
    def gv(z):return (2-z) if typ=='two' else (3-z)/(1+z)
    return gv(bh)/b,gv(al)/a
def finite(c,K,t,typ):
    lam=Q(0)
    for _ in range(t):
        p=1-em(lam)[1]; check(0<=p<1)
        prob=[Q(1),Q(1)]+[Q(1,2**(l-2)) for l in range(3,K+1)] if typ=='uni' else [Q(1)]*2
        lam=rd(sum(v*p**i for i,v in enumerate(prob))/c)
    # (1+lambda)e^-lambda decreases with lambda, so use a lower input for an upper bound.
    margin=1-(1+lam)*em(lam)[1]-2*(1-1/c)
    check(margin>0)
    return margin
for typ,L,H,K,c in [('two','1.25532039069','1.25532039070',2,'1.2553203906'),('uni','1.36145148634','1.36145148635',40,'1.3614514863')]:
    low,high=critical(typ)
    check(Q(L)<low<=high<Q(H))
    m=finite(Q(c),K,40,typ)
    print(typ,'critical ratio in',L,H,'; T=40 K='+str(K),'margin at',c,'>',Q((10**14*m).__floor__(),10**14))
# Exact finite geometric-rank law: simplex volume by direct integer order counts in
# a grid limit can illustrate but is not used; instead check all finite mark generators.
for K in range(2,30):
    tails=[Q(1),Q(1)]+[Q(1,2**(i-2)) for i in range(3,K+1)]
    mass=[tails[i]-(tails[i+1] if i+1<K else 0) for i in range(K)]
    check(all(q>=0 for q in mass) and sum(mass)==1)
    for p in (Q(0),Q(1,5),Q(3,4),Q(1)):
        mixed=sum(mu*sum(p**i for i in range(l+1)) for l,mu in enumerate(mass))
        check(mixed==sum(s*p**i for i,s in enumerate(tails)))
print('28 finite mark distributions checked by both tail and length expansions.')
