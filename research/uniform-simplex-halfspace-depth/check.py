"""Auxiliary planar consistency check; not a finite replacement for the analytic proof."""
from fractions import Fraction as F
from itertools import product
from math import gcd

def need(ok, message):
    if not ok: raise ArithmeticError(message)

def cap(u, offset):
    tri = [(F(0),F(0)),(F(1),F(0)),(F(0),F(1))]
    out = []
    for P,Q in zip(tri,tri[1:]+tri[:1]):
        a,b = (u[0]*x+u[1]*y-offset for x,y in (P,Q))
        if a >= 0: out.append(P)
        if (a>0 and b<0) or (a<0 and b>0):
            w = a/(a-b)
            out.append(tuple(p+w*(q-p) for p,q in zip(P,Q)))
    return abs(sum(p[0]*q[1]-p[1]*q[0] for p,q in zip(out,out[1:]+out[:1])))

points = list(product([F(i,24) for i in range(1,8)], repeat=2))
normals = [(i,j) for i,j in product(range(-8,9),repeat=2) if gcd(i,j)==1]
count=0
for x,y in points:
    target=4*x*y
    for i,j in normals:
        need(cap((i,j),i*x+j*y)>=target,"lower bound via exact polygon clipping")
        count+=1
    need(cap((-y,-x),-2*x*y)==target,"attaining cut")
need(len(points)==49 and count==8624,"enumeration incomplete")
print(f"PASS: {count} exact competing triangle caps, {len(points)} exact attaining cuts")
