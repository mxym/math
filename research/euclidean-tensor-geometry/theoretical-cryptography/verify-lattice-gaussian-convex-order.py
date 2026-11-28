#!/usr/bin/env python3
"""Synthetic reproduction checks for the lattice Gaussian convex-order proof."""
from fractions import Fraction as F
from itertools import product
import mpmath as mp

mp.mp.dps = 65


def exact_coefficients():
    # B_n coefficients in x=δ-1/2, constant first.
    B2 = (F(-1,12), F(0), F(1))
    B3 = (F(0),F(-1,4),F(0),F(1))
    B4 = (F(7,240),F(0),F(-1,2),F(0),F(1))
    for poly, previous in ((B3,B2),(B4,B3)):
        n=len(poly)-1
        assert tuple(i*poly[i] for i in range(1,len(poly))) == tuple(n*c for c in previous)
    d0=-B2[0]
    phase_optimum=F(1,288)
    bcoef=-B4[0]/8-d0*d0/8
    assert d0==F(1,12)
    assert bcoef==F(-13,2880)
    assert bcoef+phase_optimum==F(-1,960)
    assert -2*bcoef==F(13,1440)
    for u in (F(1,100),F(1,3),F(1),F(7)):
        deriv=-1/(1+u)+2/(1+u)**2-1
        assert deriv == -u*(3+u)/(1+u)**2 and deriv<0
    return d0,-2*bcoef


def geometric():
    tests=0
    for b in map(mp.mpf, ('.07','.13','.5','1','2','4','8','20','50')):
        u=mp.exp(-b)
        f=lambda x: b*b*mp.exp(-b*x)*(x/(1-u)+u/(1-u)**2)
        mode=1/b-u/(1-u)
        assert 0 < mode < 1
        assert abs(mp.diff(f,mode)) < mp.mpf('1e-58')
        assert mp.log(f(mode)) < b*b/24
        assert mp.almosteq(f(0),f(1))
        assert mp.almosteq(mp.log(f(mode)),mp.log((b/2)/mp.sinh(b/2))-1+(b/2)*mp.coth(b/2))
        for j in range(81):
            assert f(mp.mpf(j)/80)<=f(mode)
            tests+=1
    return tests


class Model:
    def __init__(self,v,a):
        self.v=mp.mpf(v)
        self.a=mp.mpf(a)
        self.M=int(mp.ceil(18*mp.sqrt(v)+2))
        points=[self.a+j for j in range(-self.M,self.M+1)]
        masses=[mp.exp(-x*x/(2*self.v)) for x in points]
        self.Z=mp.fsum(masses)
        self.m=mp.fsum(x*q for x,q in zip(points,masses))/self.Z
    def D(self,t):
        j0=int(mp.ceil(t-self.a))
        x0=self.a+j0
        return mp.fsum((x0+j-t)*mp.exp(-(x0+j)**2/(2*self.v))
                       for j in range(self.M+1))/self.Z
    def C(self,w,t):
        y=t-self.m
        return mp.sqrt(w/(2*mp.pi))*mp.exp(-y*y/(2*w))-y*mp.erfc(y/mp.sqrt(2*w))/2
    def d0(self):
        return mp.mpf(1)/12+mp.mpf(13)/(1440*self.v)


def numerical():
    half, broader=0,0
    maxerr=mp.mpf(0)
    for v,a in product((9,16,36,64,144,256),('0','.13','0.5','.83')):
        M=Model(v,a)
        t=(M.a-mp.mpf('.5')) % 1
        assert 0 <= t < 1
        d=M.D(t)
        root=mp.findroot(lambda u: M.C(M.v+u,t)-d,('.08','.09'))
        err=abs(root-M.d0())*M.v**2
        assert err < mp.mpf('.008')
        maxerr=max(err,maxerr)
        half+=1
        for j in (0,1,2,3,4,6,12,20,int(v)//2,int(v),2*int(v),10*int(v)):
            for f in ('0.1','0.49','0.52','0.9'):
                t=mp.mpf(j)+mp.mpf(f)
                assert M.C(M.v+M.d0()+mp.mpf('.02')/M.v**2,t)>M.D(t)
                broader+=1
    return half,broader,mp.nstr(maxerr,9)


def main():
    print("PASS exact inflation coefficients:",exact_coefficients())
    print("PASS geometric tilted-tail maxima:",geometric())
    print("PASS half-cell roots and padded toy strikes (counts, max scaled error):",numerical())


if __name__=="__main__":
    main()
