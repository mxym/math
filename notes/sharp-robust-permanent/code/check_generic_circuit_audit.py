#!/usr/bin/env python3
"""Exact generic rectangular-matrix audit of the circuit/maximal-minor theorem.

Compares a SymPy nullspace circuit enumerator with an independent integer
Bareiss-cofactor enumeration on rank-full matrices with first row all ones.
Finite cross-checks only; the general mathematical proof is in paper.md.
"""
import random
import itertools
from fractions import Fraction
from sympy import Matrix
from check_universal_max_minors import det_int

def ratio(c):
    d=sum(abs(int(v)) for v in c)
    assert d>0
    return Fraction(2*abs(int(c[0])),d)

def fullminor(M):
    r=len(M)
    p=len(M[0])
    best=Fraction(0)
    for I in itertools.combinations(range(1,p),r):
        J=(0,)+I
        vec=[(-1)**j*det_int([[M[a][J[b]] for b in range(r+1) if b!=j]
                             for a in range(r)]) for j in range(r+1)]
        if any(vec):
            assert all(sum(M[a][J[j]]*vec[j] for j in range(r+1))==0 for a in range(r))
            best=max(best,ratio(vec))
    return best

def allcircuits(M):
    r=len(M);p=len(M[0])
    best=Fraction(0)
    for sz in range(2,min(r+1,p)+1):
        for I in itertools.combinations(range(1,p),sz-1):
            J=(0,)+I
            A=Matrix([[M[a][j] for j in J] for a in range(r)])
            B=A.nullspace()
            if len(B)!=1 or any(c==0 for c in B[0]):continue
            d=1
            for c in B[0]:
                d=d*c.q//__import__('math').gcd(d,c.q)
            vec=[int(c*d) for c in B[0]]
            best=max(best,ratio(vec))
    return best

def main():
    rnd=random.Random(20261008)
    total=0
    for r in range(2,6):
        for p in (r+1,r+2,r+3):
            for trial in range(18):
                M=[[1]*p]
                M += [[rnd.randrange(-3,4) for j in range(p)] for i in range(r-1)]
                if trial%5==0:
                    # Exact duplicates produce non-maximal circuits.
                    for i in range(r):M[i][1]=M[i][0]
                if Matrix(M).rank()!=r:continue
                ref=allcircuits(M)
                got=fullminor(M)
                assert ref==got,(r,p,trial,ref,got,M)
                total+=1
    print('GENERIC FULL-RANK CIRCUIT/COFACTOR EXACT AUDIT PASSED',total,'matrices')
if __name__=='__main__':main()
