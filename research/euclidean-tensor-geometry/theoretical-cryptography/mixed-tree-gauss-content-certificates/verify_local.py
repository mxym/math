"""Finite exact tests of endpoint contents and the binary matrix criterion."""
from fractions import Fraction
from itertools import combinations
from math import gcd

def det(mat):
    A=[list(map(Fraction,row)) for row in mat]
    z=1
    for i in range(len(A)):
        j=next((j for j in range(i,len(A)) if A[j][i]),None)
        if j is None: return 0
        if i!=j:
            A[i],A[j]=A[j],A[i]
            z=-z
        x=A[i][i]
        z*=x
        for j in range(i+1,len(A)):
            q=A[j][i]/x
            for h in range(i,len(A)): A[j][h]-=q*A[i][h]
    assert z.denominator==1
    return int(z)

def check_block(forms):
    # rows in increasing affine degree, all homogenized to degree m.
    m=len(forms[0])-1
    assert gcd(*forms[0])==gcd(*forms[-1])==1
    cols=[[0]*i+list(f)+[0]*(m-i-1) for f in forms for i in range(m)]
    vals=[det(A) for A in combinations(cols,2*m)]
    return gcd(*vals)

Hvals=[0,1,-1,2,-2,7,-19,2**128,-2**255,2**500]
for H in Hvals:
    F=[[-2,-3*H-15,-1],[0,H,1],[1,0,0]] # ordered by Y degree
    assert all(check_block(forms)==1 for forms in (F,list(zip(*F))))
    assert sum(a*7**i*3**j for j,row in enumerate(F) for i,a in enumerate(row))==0

# Two old-slice catalogue edges: certificates at the edge level.
for L in range(4,133):
    C=3*2**(L-2)
    FF=[[1,-(C+1)],[0,1]]
    GG=[[-1,-1],[1,0]]
    for F in (FF,GG):
        assert check_block(F)==check_block(list(zip(*F)))==1
    assert (C+1)-1==C and C.bit_length()==L
    assert 2**(L-2)*3==C

# Known bad examples for the full-minor criterion.
assert det([[2,0],[0,1]])==2
assert det([[2,0],[4,0]])==0

print("PASS local edge certificates: 20 quadratic direction checks; 516 linear direction checks; 129 old-slice instances; 2 bad matrices.")
