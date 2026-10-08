#!/usr/bin/env python3
"""Exact scalar replay for all-rank 5/14 stability class-mass estimates.

The only machine-assisted infinite-group statement is the certified
1/250 noncontact dual gap in check_allrank_stability_gap.py. This
additional tiny Fraction checker verifies the invertible two-moment
matrix and explicit inverse operator bounds in the written proof.
"""
from fractions import Fraction as F


def require(cond, msg):
    if not cond:
        raise ArithmeticError(msg)


def main():
    values=[]
    for q in (F(1,2), F(1,6)):
        t=q*(1-q)
        K=1-4*t+2*t*t
        T=1-2*t
        E=(1-3*t)**2
        values.append((1-K,E-T))
    (a,b),(c,d)=values
    det=a*d-b*c
    require(values == [(F(7,8),F(-7,16)),
                       (F(335,648),F(-55,144))],
            "bad two-moment entries")
    require(det==F(-35,324), "two-moment determinant not invertible")
    row1=(abs(d)+abs(b))/abs(det)
    row2=(abs(c)+abs(a))/abs(det)
    require(row1==F(531,70) and row2==F(451,35),
            "incorrect inverse matrix row sums")
    require(F(33,50)-F(9,14)>F(1,250),
            "tail lower-contact separation insufficient")
    require(1-F(47,50)>F(1,250),
            "tail upper-contact separation insufficient")
    print("EXACT TWO-MOMENT MATRIX:",values)
    print("EXACT DETERMINANT:",det)
    print("EXACT CLASS-MASS ERROR FACTORS:",row1,row2)
    print("ALL-RANK STABILITY SCALAR CERTIFICATE PASS")


if __name__=="__main__":
    main()
