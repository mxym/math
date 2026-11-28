"""Finite projective certificates and an exact four-component deformation; no solver."""
from itertools import product
from math import prod
from fractions import Fraction

# Symbolic tree shape: affine factors of D,V,B as (slope,intercept,exponent).
I=([(1,0,1)],[],[(1,-1,1)])
P=([(2,1,1)],[(1,0,3)],[(1,-1,1)])
Q=([(2,1,1),(4,1,1)],[(1,0,2)],[(1,-1,1),(1,0,1)])
L=([(4,3,1)],[(1,0,2),(2,1,3)],[(1,-1,1)])
M=([(4,1,1),(4,3,1)],[(1,0,3),(2,1,2)],[(1,-1,1),(1,0,1)])
trees=[I,P,Q,L,M]; nontriv=trees[1:]
def ev(F,t,prime):
    # Return (homogeneous numerator, coordinate denominator to its full degree).
    if t is None:
        return prod(pow(a,e,prime) for a,b,e in F)%prime, int(not F)
    return prod(pow((a*t+b)%prime,e,prime) for a,b,e in F)%prime, 1

fields=[13,17,19,23]; three=two=0
for prime in fields:
    pts=list(range(prime))+[None]
    for X,Y,Z in product(trees,nontriv,nontriv):
        for y,z in product(pts,repeat=2):
            simultaneous=True
            for j,K in enumerate((2,3,5)):
                nums=[]; dens=[]
                for tree,t in zip((X,Y,Z),(1,y,z)):
                    u,v=ev(tree[j],t,prime);nums.append(u);dens.append(v)
                if (prod(nums)-K*prod(dens))%prime:
                    simultaneous=False;break
            assert not simultaneous
            three+=1
    for X,Y in product(nontriv,nontriv):
        for y in pts:
            eq=[]
            for j,K in ((0,2),(1,3)):
                u,v=ev(X[j],0,prime);w,z=ev(Y[j],y,prime)
                eq.append((u*w-K*v*z)%prime==0)
            assert not all(eq)
            two+=1

roots=(23,29,41,53); support=roots+tuple(2*x+1 for x in roots)
assert {(p,q) for p in support for q in support if (q-1)%p==0}=={(p,2*p+1) for p in roots}
def f(t): return prod(t-r for r in roots)
def fz(t,z): return f(t)+z*t*(t-1)*(2*t+1)
parameters=range(-12,13)
for z in parameters:
    for t in (0,1,Fraction(-1,2)):
        assert fz(t,z)==f(t)
assert len({fz(2,z) for z in parameters})==len(parameters)
print("empty projective fibers over F_p: three-variable points",three,"two-variable points",two)
print("four-component deformation parameters",len(parameters),"invariants at three arguments unchanged")
