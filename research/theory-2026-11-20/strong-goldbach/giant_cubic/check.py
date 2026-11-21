"""Finite identities and rational slack checks. Analytic estimates are proved in Proof.md."""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement

def require(ok, msg):
    if not ok: raise ArithmeticError(msg)

def transform(xs, D):
    return sum((-1)**k * max(D-2*sum(S),0)**3 for k in range(len(xs)+1) for S in combinations(xs,k))
size=0
for j in range(1,7):
    for rs in combinations_with_replacement(range(1,12),j):
        t=sum(rs)
        D=49
        if 2*t>=D: continue
        true=transform(rs+(D-t,),D)
        if j==1:
            u,=rs; expected=6*u*D**2-12*u*u*D+8*u**3
        elif j==2:
            u,v=rs; expected=24*u*v*(D-t)
        elif j==3:
            u,v,w=rs; expected=48*u*v*w
        else: expected=0
        require(true==expected and true>=0,(rs,true,expected));size+=1
# Integrals as a pair of coefficients of (1, log 2).
coeffs=[(1,2),(F(3,2),0),(F(-5,2),4)]
require(tuple(map(sum,zip(*coeffs)))==(0,6),'angular integrals')
# log 2 = 2 atanh(1/3), lower bound by a positive rational partial.
lb=2*sum(F(1,(2*j+1)*3**(2*j+1)) for j in range(8))
require(6*(6-F(200,53))==F(708,53),'sieve coefficient')
require(F(708,53)*lb>F(37,4),'strict 9.25')
print(f'checked {size} integral giant profiles across cofactor sizes 1,...,6; M=6 log 2; oriented constant > 9.25')
