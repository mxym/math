"""Rank-33 Hoffman residual: exact E7 shell constants, dyadic checks, theta arithmetic.
Python 3.8+, no dependencies. No graph or search over graph candidates.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product

def walk(v, budget):
    if len(v)==8:
        if sum(v)%4==0:
            yield tuple(v)
        return
    p=v[0]%2 if v else None
    for x in range(-4,5):
        if x*x<=budget and (p is None or x%2==p):
            yield from walk(v+[x],budget-x*x)

# Twice the usual E8 coordinates; take alpha=(1,-1,0^6).
D=Counter()
for v in walk([],16):
    n,rem=divmod(sum(t*t for t in v),4)
    assert rem==0
    a,rem=divmod(v[0]-v[1],2)
    assert rem==0
    D[n,a]+=1
assert [D[2,0],D[4,0],D[2,1],D[4,1]]==[126,756,56,576]
# E7 axis moment from irreducible Weyl invariance.
assert [n*c/7 for n,c in [(2,126),(4,756),(F(3,2),56),(F(7,2),576)]]==[36,432,12,288]
# theta_U = E4^5 + (R-1200) Delta E4^2.
assert 5*240==1200 and 5*2160+10*240**2-1200*(2*240-24)==39600
assert 2*240-24==456 and -264-24==-288
# Check polynomial identity of affine expressions by five probes.
for a,r,b in [(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,17,30)]:
    N2=126+r+56*a
    N4=39600+456*N2
    lhs=432+36*r+288*a+12*b+288*(36+12*a)
    rhs=F(4*N4+576*N2,40)
    assert lhs-rhs==12*(b-60-2*r+32*a)
# At odd 7 the two-dimensional anisotropic finite plane has negative Gauss sign;
# orthogonal sum flips that sign for each anisotropic residual plane.
# At two inspect the elementary diagonal/alternating cases of the text.
survivors=[]
for s in (+1,-1):
    for k,aplane in product(range(4),range(2)):
        if aplane and k>1: continue
        if (k+2*aplane)%2==0: continue
        if (s*k+4*aplane-1)%8:continue
        survivors.append((s,k,aplane))
assert survivors==[(1,1,0)]
print("E7 shells 126 756; dual coset shells 56 576.")
print("T determinant 2: B70 = 60 + 2 R56 - 32 A14, with A14 in {0,2}.")
