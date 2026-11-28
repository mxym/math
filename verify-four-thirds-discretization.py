#!/usr/bin/env python3
"""Finite checks for the exact four-thirds Gaussian comparison proof."""
from fractions import Fraction as F
from math import pi
import mpmath as mp

mp.mp.dps=65


def exponents():
    n=0
    for t in (4,5,6,9,11,20,50,101):
        Delta=F(t*t,3)+2
        L=1+F(t*t)/Delta
        d=4-L
        lam=2-d/4
        assert Delta*d==6 and 3<L<4
        assert L/2<lam<2 and 1<L-lam<lam
        assert (L-1)*(2*lam-L)+(L-lam-1)**2-(lam-1)**2==d/2
        assert 1+(2-lam)**2-(lam-1)**2==d/2
        assert (L-1)*(4-L)+(L-3)**2==5-L
        assert 1-(lam-1)**2==d/2-d*d/16>=7*d/16
        assert 2*(1+16)*6*mp.exp(-mp.mpf(21)*mp.pi/8) + 12*mp.exp(-4*mp.pi*mp.mpf(22)/3) < 1
        n+=1
    return n


def finite_schur():
    out=[]
    for t in (4,5,8,16,30):
        Delta=mp.mpf(t*t)/3+2
        L=1+t*t/Delta
        d=4-L
        lam=2-d/4
        D=mp.exp(-mp.pi*Delta)
        P=mp.exp(-mp.pi*Delta*(lam-1)**2)
        V=mp.exp(-mp.pi*Delta*(2-lam)**2)
        def q(a):
            return mp.exp(-mp.pi*Delta*a*a)
        def T(j,k):
            ell=lam if k==1 else k
            mu=ell-L
            b=mp.exp(-mp.pi*t*t*(2*ell-L))
            return q(j-ell)+q(j+ell)-b*(q(j-mu)+q(j+mu))
        high=range(2,15)
        B=mp.matrix([[T(j,k) for k in high] for j in high])
        row=[T(1,k) for k in high]
        col=mp.matrix([T(j,1) for j in high])
        f=mp.matrix([-2*q(j) for j in high])
        assert max(abs(z) for z in row)<=4*D
        assert sum(abs(z) for z in col)<=8*V
        assert max(sum(abs(B[i,j]-(i==j)) for i in range(len(high)))
                   for j in range(len(high)))<mp.mpf('.5')
        y=mp.lu_solve(B,col)
        z=mp.lu_solve(B,f)
        S=T(1,1)-mp.fdot(row,y)
        assert S>P/2
        c1=(-2*D-mp.fdot(row,z))/S
        C=[c1]+list(z-c1*y)
        size=sum(abs(c) for c in C)
        assert abs(c1)<=6*D/P and 2*size<1
        assert max(abs(mp.fdot([T(j,k) for k in range(1,15)],C)+2*q(j))
                   for j in range(1,15)) < mp.mpf('1e-58')
        out.append((t,mp.nstr(S/P,9),mp.nstr(size,9)))
    return out


def main():
    print("PASS rational exponent identities:",exponents())
    print("PASS finite illustrative Schur blocks (t, S/P, coefficient l1):",finite_schur())


if __name__=="__main__":
    main()
