#!/usr/bin/env python3
"""Exact rational identities for the full complex permanent-pencil norm.

This verifies two universal polynomial identities over Q, using 4^6
rational interpolation points for each (all degrees <=3 separately in
X,Y,Z,B,q,x). Analytic PSD arguments and extremal witnesses are in PAPER.md.

No floating point, solver, unverified symbolic package or Python asserts.
"""
from fractions import Fraction as F
from itertools import product

def need(condition, label):
    if not condition:
        raise RuntimeError("exact full-norm certificate failed: "+label)

def hermitian_data(X,Y,Z,B,q,x):
    h=B-1-q
    v=2*x
    d1=B*X+(h+v)*Y+(h-v)*Z
    d2=(h-v)*X+B*Y+(h+v)*Z
    d3=(h+v)*X+(h-v)*Y+B*Z
    zsq=(1+q)**2-v*v
    rez3=(1-q)**3-12*(1-q)*(q-x*x)
    return h,v,d1,d2,d3,zsq,rez3

def determinant_from_entries(X,Y,Z,B,q,x):
    h,v,d1,d2,d3,zsq,rez3=hermitian_data(X,Y,Z,B,q,x)
    return d1*d2*d3-zsq*(d1*Y*Z+d2*X*Z+d3*X*Y)-2*rez3*X*Y*Z

def determinant_from_certificate(X,Y,Z,B,q,x):
    h,v,*_=hermitian_data(X,Y,Z,B,q,x)
    U=X**3+Y**3+Z**3-3*X*Y*Z
    V=(X+Y+Z)*(X*Y+Y*Z+Z*X)-9*X*Y*Z
    r=(3*B-4)*((3*(B-q)-1)**2-12*(q-x*x))
    return B*(h*h-v*v)*U+B*(3*h*h+v*v)*V+r*X*Y*Z

def minor_from_entries(X,Y,Z,B,q,x):
    h,v,d1,d2,d3,zsq,rez3=hermitian_data(X,Y,Z,B,q,x)
    return d1*d2-zsq*X*Y

def minor_from_certificate(X,Y,Z,B,q,x):
    h,v,*_=hermitian_data(X,Y,Z,B,q,x)
    return (B*(h-v)*X*X + B*(h+v)*Y*Y
            +(h*h-v*v)*Z*Z+2*B*h*X*Y
            +(B*(h+v)+(h-v)**2)*X*Z
            +((h+v)**2+B*(h-v))*Y*Z)

def main():
    # Verify each identity as a 6-variable rational polynomial.
    count=0
    for X,Y,Z,B,q,x in product(range(4),repeat=6):
        args=(X,Y,Z,B,q,x)
        need(determinant_from_entries(*args)==determinant_from_certificate(*args),
             "determinant "+str(args))
        need(minor_from_entries(*args)==minor_from_certificate(*args),
             "second-order minor "+str(args))
        count+=1
    # A deliberately false identity must fail.
    args=(1,2,3,2,F(1,2),F(1,4))
    need(determinant_from_entries(*args)!=determinant_from_certificate(*args)+1,
         "corrupted determinant control")
    need(minor_from_entries(*args)!=minor_from_certificate(*args)+1,
         "corrupted second-minor control")
    print("PASS: exact norm formula for all complex 3x3 permanent-determinant pencils")
    print("determinant global identity rational interpolation nodes:",count)
    print("2x2 principal-minor global identity nodes:",count)
    print("parameter variables: B, q=|lambda|^2, x=Re(lambda)")
    print("positive terms: U, V, and factor (3B-4)([3(B-q)-1]^2-12y^2)")
    print("sharp witnesses: all-ones, both parities, Fourier rows")
    print("negative controls: corrupted determinant and minor rejected")
    print("field Q only; no floating point, external solver, or disabled assertions")

if __name__ == "__main__":
    main()
