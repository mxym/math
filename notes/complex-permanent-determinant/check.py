#!/usr/bin/env python3
"""Exact self-contained Q(sqrt(3)) polynomial-identity checker.

This checks the algebraic equalities needed for the complex 3x3
permanent-determinant inequality. No floating point, no external solver,
no Python asserts (checks persist under -O). Analytic AM-GM / principal
minor arguments are proved in PAPER.md.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

def require(condition, message):
    if not condition:
        raise RuntimeError("exact certificate failed: " + message)

@dataclass(frozen=True)
class Q3:
    a: F
    b: F

    def __init__(self, a=0, b=0):
        object.__setattr__(self, "a", F(a))
        object.__setattr__(self, "b", F(b))

    def __add__(self, other):
        v = to_q3(other)
        return Q3(self.a + v.a, self.b + v.b)
    __radd__ = __add__

    def __neg__(self):
        return Q3(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-to_q3(other))

    def __rsub__(self, other):
        return to_q3(other) - self

    def __mul__(self, other):
        v = to_q3(other)
        return Q3(self.a*v.a+3*self.b*v.b, self.a*v.b+self.b*v.a)
    __rmul__ = __mul__

    def __pow__(self, n):
        require(isinstance(n,int) and n>=0, "power natural")
        r=Q3(1)
        x=self
        while n:
            if n&1:
                r=r*x
            n//=2
            x=x*x
        return r

def to_q3(x):
    return x if isinstance(x,Q3) else Q3(x)

S = Q3(-1, F(2,3))  # 2/sqrt(3)-1 > 0
R2 = Q3(F(4,3))      # rho squared, rho=2/sqrt(3)

def diags(X,Y,Z,t):
    return (
        R2*X + (2*S+2*t)*Y + (2*S-2*t)*Z,
        (2*S-2*t)*X + R2*Y + (2*S+2*t)*Z,
        (2*S+2*t)*X + (2*S-2*t)*Y + R2*Z,
    )

def off_abs_sq(t):
    # |1-s^2+2iy|^2, when |lambda|=s and y^2=s^2-t^2.
    return (1+S**2)**2 - 4*t*t

def det_direct(X,Y,Z,t):
    d1,d2,d3=diags(X,Y,Z,t)
    # Re((1-s^2+2iy)^3) at y^2=s^2-t^2.
    z_re_cube=(1-S**2)**3-12*(1-S**2)*(S**2-t*t)
    return (d1*d2*d3
            -off_abs_sq(t)*(d1*Y*Z+d2*X*Z+d3*X*Y)
            -2*z_re_cube*X*Y*Z)

def det_sos(X,Y,Z,t):
    a=X**3+Y**3+Z**3-3*X*Y*Z
    b=(X*X*Y+X*X*Z+Y*Y*X+Y*Y*Z+Z*Z*X+Z*Z*Y
       -6*X*Y*Z)
    return 4*R2*((S*S-t*t)*a+(3*S*S+t*t)*b)

def minor_direct(X,Y,Z,t):
    d1,d2,_=diags(X,Y,Z,t)
    return d1*d2-off_abs_sq(t)*X*Y

def minor_positive_coefficients(X,Y,Z,t):
    return (
        R2*(2*S-2*t)*X*X
        +R2*(2*S+2*t)*Y*Y
        +4*(S*S-t*t)*Z*Z
        +4*S*R2*X*Y
        +(R2*(2*S+2*t)+(2*S-2*t)**2)*X*Z
        +(R2*(2*S-2*t)+(2*S+2*t)**2)*Y*Z
    )

def main():
    require((1+S)**2==R2,"sharp coefficient rho²=4/3")
    require(S*S+2*S==Q3(F(1,3)),"quadratic field reduction")
    # The compared sides have degree <= 3 in EACH of X,Y,Z,t.
    # By iterated one-variable polynomial interpolation, equality
    # at the complete 4x4x4x4 rational grid proves identity globally.
    checked=0
    for X,Y,Z,t in product(range(4),repeat=4):
        require(det_direct(X,Y,Z,t)==det_sos(X,Y,Z,t),
                "det H identity at "+str((X,Y,Z,t)))
        require(minor_direct(X,Y,Z,t)==minor_positive_coefficients(X,Y,Z,t),
                "two-minor identity at "+str((X,Y,Z,t)))
        checked+=1
    # Hostile changes must be detected by the same equality comparison.
    require(det_direct(1,1,0,0)!=det_sos(1,1,0,0)
            +4*R2*S*S*2,
            "invalid 2s² mixed coefficient was not detected")
    require(minor_direct(1,1,1,0)!=minor_positive_coefficients(1,1,1,0)
            +R2,
            "corrupted two-minor polynomial was not detected")
    print("PASS: sharp complex 3x3 permanent-determinant certificate")
    print("exact coefficient field: Q(sqrt(3)), fractions only")
    print("determinant SOS identity evaluations:",checked)
    print("principal 2x2 minor identity evaluations:",checked)
    print("proof: degree-at-most-three interpolation in four variables")
    print("negative controls: two corrupted formulas rejected")
    print("analytic PSD step: AM-GM plus all principal minors (PAPER.md)")
    print("sharp endpoints: identity and constant matrices")
    print("no floating point, no solver, no disabled assertions")

if __name__ == "__main__":
    main()
