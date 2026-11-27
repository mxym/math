"""Exact arithmetic checks for FactorShortSalemNormGap.md."""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd

checks = 0


def check(x):
    global checks
    assert x
    checks += 1


def directions():
    p = []
    for z in range(3):
        for s in (1,-1):
            d = [1,s]
            d.insert(z,0)
            p.append(tuple(d))
    t = [(1,a,b) for a,b in product((1,-1),repeat=2)]
    return p,t


def normal(d,e):
    a,b,c=d
    r,s,t=e
    v=(b*t-c*s,c*r-a*t,a*s-b*r)
    f=gcd(*v)
    f=f if next(x for x in v if x) > 0 else -f
    return tuple(x//f for x in v)


def ordered_cone(v):
    a,b,c=v
    # A=C+v1+v2, B=C+v1. All three independent variables positive.
    coeff=(a+b+c,a+b,a)
    return min(coeff)<0<max(coeff)


def check_directions():
    pairs,triples=directions()
    d=pairs+triples
    exception={}
    for a,b in combinations(d,2):
        v=normal(a,b)
        check(sum(map(abs,v))<=4)
        if a in triples and b in triples:
            check(sum(map(abs,v))<=2)
        if (a in pairs) != (b in pairs):
            check(any(abs(a[i]*b[j]-a[j]*b[i])==1
                      for i,j in combinations(range(3),2)))
        if ordered_cone(v):
            exception.setdefault(v,set()).add(frozenset([a,b]))
    P=(0,1,-1)
    Q=(1,0,1)
    R=(1,1,0)
    expect={(1,-1,-1): {frozenset(x) for x in combinations((P,Q,R),2)},
            (1,-2,-1): {frozenset([Q,(1,1,-1)])},
            (1,-2,1): {frozenset([(1,0,-1),(1,1,1)])},
            (1,-1,-2): {frozenset([R,(1,-1,1)])}}
    check(exception==expect)


def check_hexagon():
    lim=F(16,27)
    h=lambda u:F(4,27)*u**3*(u-2)**2*(u-3)**2
    check(h(F(1))==lim)
    check(h(F(18,7))<lim)
    check(h(F(3))==0)
    check(h(F(2))==0)
    check(h(F(0))==0)
    for n in range(-24,25):
        for m in range(-24,25):
            if abs(n+m)>24: continue
            x,y,z=F(n,12),F(m,12),F(-n-m,12)
            u=(x*x+y*y+z*z)/2
            v=x*y*z
            check(u==-x*y-x*z-y*z and 0<=u<=4)
            check(v*v<=F(4,27)*u**3 and abs(v)<=8-2*u)
            check((v*(u-2)*(u-3))**2<=lim)


def norm_contradiction(n,d,b):
    # eta_0**(d-2) > 1024*b**(7*n)
    k=d-2
    t=7*n
    return 1299**k*b.denominator**t > 1024*1000**k*b.numerator**t


def check_thresholds():
    eta0=F(1299,1000)
    check(eta0**2<F(27,16))
    A=F(101,100)
    B=F(10011,10000)
    check(100*32*7200<=F(4,9)*7200**2)
    check(F(7200,2)+576<=F(2,3)*7200)
    check(100*32*4200<=F(49,64)*4200**2)
    check(F(4200,2)+576<=F(7,8)*4200)
    for n0,s,b in [(7200,3,A),(4200,8,B)]:
        check(eta0>b**(7*s))
        for n in range(n0,n0+s):
            check(norm_contradiction(n,n//s-300,b))
    check(norm_contradiction(4199,154,B))
    check(B**608<2)
    check(norm_contradiction(40,40,A))
    check(eta0>A**7)


if __name__=="__main__":
    check_directions()
    check_hexagon()
    check_thresholds()
    print(f"Length-six Salem gap: {checks} exact checks passed.")
