#!/usr/bin/env python3
# Finite consistency checks for the fiber-square geometry and residue obstruction;
# this does not numerically check the analytic infinite theorem.
from itertools import combinations
from math import gcd,prod
from fractions import Fraction
def check(ok):
    if not ok: raise AssertionError
def normalized(v):
    a=next(z for z in v if z)
    return tuple(Fraction(z,a) for z in v)
def test(forms):
    n=len(forms[0])
    def independent(F):
        check(len({normalized(v) for v in F})==len(F))
    independent(forms)
    for j,a in enumerate(forms):
        r=next(k for k,z in enumerate(a) if abs(z)==1)
        non=[k for k in range(n) if k!=r]
        # y=a*x+c, u=all coordinates except x_r; ignore constants.
        def mapped(b):
            s=b[r]//a[r]
            return [s]+[b[k]-s*a[k] for k in non]
        f=[[1]+[0]*(2*n-2)]
        for i,b in enumerate(forms):
            if i==j: continue
            m=mapped(b)
            f.extend([[m[0]]+m[1:]+[0]*(n-1),[m[0]]+[0]*(n-1)+m[1:]])
        independent(f)
    return (len(forms),len(forms)*2-1)
for d in (3,6):
    v=[[int(k==i) for k in range(d+1)] for i in range(d+1)]
    w=[tuple(v[(i+1)%d][j]+v[d][j] for j in range(d+1)) for i in range(d)]
    t=[tuple(v[i][j]+w[i][j] for j in range(d+1)) for i in range(d)]
    print('cyclic',d,'forms/doubled',test(v[:d]+w+t))
print('lifts forms/doubled',test([(1,0),(0,1),(1,1)]))
for x,y in combinations(range(3),2):
    check((2*x-2)%3!=(2*y-2)%3)
for bits in ((2,3,5),(2,3,5,7),(2,3,5,7,11)):
    W=prod(bits); R={r for r in range(W) if gcd(r,W)==1}
    matched={r for r in R if (2-r)%W in R}
    discard={r for r in matched if r<=(2-r)%W}|{W-1}
    kept=R-discard
    check(all((2-r)%W not in kept for r in kept))
    check(W-1 not in kept and 6%W!=2)
    check(Fraction(len(matched),len(R))==prod(Fraction(q-2,q-1) for q in bits if q>2))
    print('modulus',W,'reduced/matched/deleted',len(R),len(matched),len(discard))
print('PASS')
