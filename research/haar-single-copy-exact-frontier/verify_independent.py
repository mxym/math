#!/usr/bin/env python3
"""Quadratic-field checks of the complete three-copy frontier."""
from fractions import Fraction as F
from itertools import product
from math import prod
from dataclasses import dataclass


# The radical is fixed during each test family; fields are never mixed.
RAD=3


@dataclass(frozen=True)
class Q:
    a:F
    b:F=F(0)

    def __post_init__(self):
        object.__setattr__(self,'a',F(self.a))
        object.__setattr__(self,'b',F(self.b))

    @staticmethod
    def cast(x):
        return x if isinstance(x,Q) else Q(x)

    def __add__(x,y):
        y=Q.cast(y)
        return Q(x.a+y.a,x.b+y.b)

    __radd__=__add__

    def __neg__(x):
        return Q(-x.a,-x.b)

    def __sub__(x,y):
        return x+(-Q.cast(y))

    def __rsub__(x,y):
        return Q.cast(y)+(-x)

    def __mul__(x,y):
        y=Q.cast(y)
        return Q(x.a*y.a+RAD*x.b*y.b,x.a*y.b+x.b*y.a)

    __rmul__=__mul__

    def __truediv__(x,y):
        y=Q.cast(y)
        w=y.a*y.a-RAD*y.b*y.b
        assert w
        return x*Q(y.a/w,-y.b/w)

    def __rtruediv__(x,y):
        return Q.cast(y)/x

    def sign(x):
        if x.b==0:
            return (x.a>0)-(x.a<0)
        if x.a>=0 and x.b>0:
            return 1
        if x.a<=0 and x.b<0:
            return -1
        cmp=x.a*x.a-RAD*x.b*x.b
        s=(cmp>0)-(cmp<0)
        return s if x.a>0 else -s

    def __lt__(x,y):
        return (x-y).sign()<0

    def __le__(x,y):
        return (x-y).sign()<=0

    def __gt__(x,y):
        return (x-y).sign()>0

    def __ge__(x,y):
        return (x-y).sign()>=0


def positive(x):
    x=Q.cast(x)
    return x if x.sign()>0 else Q(0)


def spectral_deficit(d,z):
    # Last-basis eigenvalues found via the Gram squared, not (9) directly.
    # The 2x2 block of the squared Gram has diag 1+z^2, offdiag 2z.
    A=F((d+1)*(d+2),d*d)
    G2_diag=1+z*z
    G2_off=2*z
    T=A-(1+z*z)
    return ((d-2)*positive(T)+
            positive(T-(G2_diag+G2_off))+
            positive(T-(G2_diag-G2_off)))


def claimed(d):
    global RAD
    RAD=66 if d==5 else 3
    if d==2:
        return Q(2),Q(-1),[(Q(0),Q(F(1,2))),(Q(1),Q(F(1,2)))],Q(F(1,4))
    if d==3:
        z=Q(0,F(1,3))
        return Q(F(13,9),F(1,3)),Q(-3,1),[(z,Q(1))],Q(F(1,15),F(1,10))
    if d==4:
        return Q(F(17,8)),Q(-2),[(Q(F(1,2)),Q(1))],Q(F(13,60))
    if d==5:
        z=Q(F(41,25),F(-4,25))
        B=5-1/z
        p=F(4,5)/(1-z*z)
        return B,-B,[(z,p),(Q(1),1-p)],Q(F(8,25),F(-8,525))
    H=F((d-2)*(3*d+2),d*d)
    return (Q(H),Q(-H),[(Q(0),Q(1-F(1,d))),(Q(1),Q(F(1,d)))],
            Q(F((3*d+2)*(d-1)*(d-2),d*d*(d+1)*(d+2))))


def frontier():
    rational_samples=0
    ineq_proofs=0
    strict=0
    for d in range(2,41):
        upper0,upper1,atoms,v=claimed(d)
        A=F((d+1)*(d+2),d*d)
        def upper(z):
            return upper0+upper1*z*z
        for i in range(81):
            z=Q(F(i,80))
            assert spectral_deficit(d,z)<=upper(z)
            rational_samples+=1
        assert sum(p for z,p in atoms)==Q(1)
        assert sum(p*z*z for z,p in atoms)==Q(F(1,d))
        assert all(0<=p and spectral_deficit(d,z)==upper(z) for z,p in atoms)
        assert sum(p*spectral_deficit(d,z) for z,p in atoms)/(d*A)==v
        # Verify a global certificate independently of the sampled grid.
        # Positive part of each term is a max over choosing either that term
        # or 0. So the entire deficit is the max of eight quadratics in z.
        for a,b,c in product((0,1),repeat=3):
            p0=upper0-a*(d-2)*(A-1)-(b+c)*(A-2)
            p1=2*(b-c)
            p2=upper1+a*(d-2)+2*(b+c)
            assert 0<=p0 and 0<=p0+p1+p2
            if 0<p2:
                z=F(-p1,2)/p2
                if 0<z<1:
                    assert 0<=p0+p1*z+p2*z*z
            ineq_proofs+=1
        if d in (3,4,5):
            pre=(F((d-1)*(d-2),d*d)*max(F(0),1-1/A)+
                 F(3*(d-1),d*d)*max(F(0),1-2/A))
            assert pre<v
            strict+=1
    return rational_samples,ineq_proofs,strict


def check_frame_averages():
    # The second-step atom-law construction, checked through projectors.
    checks=0
    for d in range(2,26):
        _,_,atoms,_=claimed(d)
        for j in range(d):
            avg=Q(0)
            for z,p in atoms:
                avg+=p*(z*z if j==0 else (1-z*z)/(d-1))
            assert avg==Q(F(1,d))
            checks+=1
    return checks


def threshold():
    # Exact near-boundary alpha checks; no float or asymptotic substitution.
    checks=0
    for t in range(2,40):
        ds=(64*t*t,64*t*t+1,80*t*t)
        for d in ds:
            A=prod(F(d+j,d) for j in range(t))
            assert 1<A<=F(65,64)<2
            assert 1-1/A <= F(t*(t-1),2*d)
            checks+=1
    return checks


if __name__ == "__main__":
    a,b,c=frontier()
    print(f"Three-round frontier: {a} exact grid points, {b} global quadratic certificates, {c} strict fixed-basis gaps")
    print(f"Attainment and birthday thresholds: {check_frame_averages()} exact POVM diagonal averages, {threshold()} finite bounds")
