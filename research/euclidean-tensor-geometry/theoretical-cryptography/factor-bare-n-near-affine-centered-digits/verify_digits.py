"""Independent exact centered-digit identities, signed windows and one false branch."""
from fractions import Fraction as Q
from itertools import product
from math import comb, isqrt, prod

def midpoint(n,r):
    # Independent integer root calculation by Newton with final checks.
    x=1 << ((n.bit_length()+r-1)//r)
    while True:
        y=((r-1)*x+n//x**(r-1))//r
        if y>=x:
            assert x**r<=n<(x+1)**r
            return x
        x=y

def decompose(values,J):
    r=len(values);K=prod(values);s=midpoint(K,r);u=[v-s for v in values]
    assert all(abs(v)**r<=J**r*s for v in u)
    # Evaluate the product polynomial by sequential convolution.
    e=[1]
    for v in u:e=[a+b*v for a,b in zip(e+[0],[0]+e)]
    assert sum(a*s**(r-i) for i,a in enumerate(e))==K
    remaining=K-s**r
    width=(1+J)**r
    for i in range(1,r+1):
        d=s**(r-i)
        delta=abs(Q(remaining,d)-e[i])
        # Exact general window, plus a separate sharper, local residual check.
        assert delta<=width
        assert delta<=sum(Q(abs(e[h]),s**(h-i)) for h in range(i+1,r+1))
        if s>(2*width)**r and i<=r-2:assert delta<Q(1,2)
        remaining-=e[i]*d
    assert remaining==0
    return s,u,e

s,u,e=decompose((12000000148404,12000000028542,11999999988542),5)
assert s==12000000055162 and tuple(u)==(93242,-26620,-66620)
assert tuple(e[1:])==(2,-6920459680,165357637904800)
K=1728000023830272026499596351466811240656
first=Q(K-s**3,s*s)
last=Q(K-s**3-e[1]*s*s,s)
assert abs(first-e[1])<Q(1,2) and 13<abs(last-e[2])<14
# Preserve the product identity but force a non-split cubic.
bad=e[:];bad[2]+=1;bad[3]-=s
assert sum(a*s**(3-i) for i,a in enumerate(bad))==K
b,c,d=-bad[1],bad[2],-bad[3]
D=b*b*c*c-4*c**3-4*b**3*d-27*d*d+18*b*c*d
assert D<0 or isqrt(D)**2!=D
# A negative offset and coincident normalized values also occur at small scale.
ss,uu,ee=decompose((18,21,18),3)
assert (ss,uu,ee)==(18,[0,3,0],[1,3,0,0])

t=neg=large=0
for r in (2,3,4):
    for ds in product(range(-2,3),repeat=r):
        # The size is a mathematical fixture, with the guaranteed high-digit
        # rounding branch exercised independently of all prime examples.
        for b0 in (20,10**12):
            s0,u0,e0=decompose(tuple(b0+d for d in ds),3)
            t+=1;neg+=any(a<0 for a in e0);large+=s0>(2*4**r)**r
print("exact centered triple",*u)
print("elementary coefficients",*e[1:],"last nontrivial displacement between 13 and 14")
print("wrong coefficient list: same evaluation, nonsquare/nonpositive discriminant")
print("signed-product fixtures",t,"with negative coefficient",neg,"in rounding regime",large)
