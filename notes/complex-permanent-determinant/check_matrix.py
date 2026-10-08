#!/usr/bin/env python3
"""Exact complex matrix-multiplication check, independent of determinant SOS.

Uses only the Fraction-based quadratic field arithmetic in check.py.
This regression verifies that the paper's Hermitian matrix H is indeed
rho^2 ||a||^2 I - M_lambda(a)^* M_lambda(a) for a finite collection
of genuinely complex matrices, both interior and boundary phases. It is NOT the proof
of the universal matrix identity; that follows by direct multiplication
in PAPER.md and the polynomial identity checker.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from check import Q3, S, R2, require

@dataclass(frozen=True)
class CQ:
    r: Q3
    i: Q3
    def __init__(self, r=0, i=0):
        object.__setattr__(self, "r", r if isinstance(r,Q3) else Q3(r))
        object.__setattr__(self, "i", i if isinstance(i,Q3) else Q3(i))
    def __add__(self, b):
        b=to_c(b)
        return CQ(self.r+b.r,self.i+b.i)
    __radd__=__add__
    def __neg__(self):
        return CQ(-self.r,-self.i)
    def __sub__(self,b):
        return self+(-to_c(b))
    def __rsub__(self,b):
        return to_c(b)-self
    def __mul__(self,b):
        b=to_c(b)
        return CQ(self.r*b.r-self.i*b.i,
                  self.r*b.i+self.i*b.r)
    __rmul__=__mul__
    def conj(self):
        return CQ(self.r,-self.i)
    def abs2(self):
        return self.r*self.r+self.i*self.i

def to_c(x):
    return x if isinstance(x,CQ) else CQ(x)

def one_minus_plus(z):
    return CQ(1)-z,CQ(1)+z

def actual_H(a,lam):
    minus,plus=one_minus_plus(lam)
    z=CQ()
    M=[[z,minus*a[2],plus*a[1]],
       [plus*a[2],z,minus*a[0]],
       [minus*a[1],plus*a[0],z]]
    normsq=sum((v.abs2() for v in a),Q3())
    mm=[[sum((M[t][i].conj()*M[t][j] for t in range(3)),CQ())
         for j in range(3)] for i in range(3)]
    return [[(CQ(R2*normsq) if i==j else CQ())-mm[i][j]
             for j in range(3)] for i in range(3)]

def check_one(a,lam):
    X,Y,Z=[z.abs2() for z in a]
    q=lam.abs2(); x=lam.r;h=Q3(F(1,3))-q;v=2*x
    d=(R2*X+(h+v)*Y+(h-v)*Z,
       (h-v)*X+R2*Y+(h+v)*Z,
       (h+v)*X+(h-v)*Y+R2*Z)
    h=actual_H(a,lam)
    for j in range(3):
        require(h[j][j]==CQ(d[j]),"direct Hermitian diagonal")
    z=CQ(1-q,2*lam.i)
    require(h[0][1]==-z*a[1].conj()*a[0],"H12")
    require(h[1][2]==-z*a[2].conj()*a[1],"H23")
    require(h[2][0]==-z*a[0].conj()*a[2],"H31")
    for i in range(3):
        for j in range(3):
            require(h[i][j]==h[j][i].conj(),"H Hermitian")
    return 1

def main():
    a_cases=[
        [CQ(1),CQ(),CQ()],
        [CQ(1),CQ(1),CQ(1)],
        [CQ(1,1),CQ(2,-3),CQ(-1,2)],
        [CQ(2),CQ(1,1),CQ(3,-1)],
        [CQ(1,-2),CQ(0,3),CQ(-4,0)],
    ]
    lambdas=[CQ(S),CQ(-S),CQ(0,S),CQ(0,-S),
             CQ(F(3,5)*S,F(4,5)*S),CQ(-F(3,5)*S,F(4,5)*S),
             CQ(),CQ(0,F(1,2)),CQ(F(1,8),F(1,4)),
             CQ(-F(1,8),F(1,4)),CQ(F(1,10),-F(1,5)),
             CQ(-F(1,10),-F(1,5))]
    checks=0
    for a in a_cases:
        for lam in lambdas:
            checks+=check_one(a,lam)
    print("PASS: complex Hermitian matrix entrywise replay")
    print("exact sample pairs (a,lambda):",checks)
    print("tested circle-boundary and interior-lens complex phases")
    print("source arithmetic: rational Q(i,sqrt(3)); no floating point")

if __name__=="__main__":
    main()
