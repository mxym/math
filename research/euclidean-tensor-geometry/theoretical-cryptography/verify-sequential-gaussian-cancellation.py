#!/usr/bin/env python3
"""Replay exact coefficient and high-precision theta comparisons for toy bases.

This uses mpmath; it does not produce cryptographic samples or benchmark a
sampler. All inputs are explicitly generated basis-level probability cases.
"""
from fractions import Fraction as F
from math import lcm
from mpmath import mp


def cos_rat(x):
    x %= 1
    values = {F(0):F(1), F(1,6):F(1,2), F(1,4):F(0),
              F(1,3):F(-1,2), F(1,2):F(-1)}
    if x>F(1,2):
        x = 1-x
    return values[x]


def J(n, rows,z):
    return sum(F(2*(-1)**(n//m+1),n//m)*cos_rat((n//m)*(c-d*z))
               for m,c,d in rows if n%m==0)


def H(n,rows,z):
    return sum(F(2*(-1)**(k+1),k)*cos_rat(k*(c-d*z))
               for m,c,d in rows if n%m==0
               for k in range(1,n//m+1)
               if (n//m)%k==0 and ((n//m)//k)%2)


def exact_coeffs():
    samples = [
        ([(1,F(0),F(1,2)),(1,F(1,2),F(1,2))],2,None),
        ([(1,F(0),F(1,3)),(1,F(1,2),F(1,3))],3,2),
        ([(1,F(0),F(1,4)),(1,F(1,2),F(1,4)),(2,F(0),F(1,2))],4,None),
        ([(1,F(0),F(1,2)),(3,F(1,3),F(1,3)),(2,F(1,6),F(0))],6,1),
        ([(1,F(1,4),F(1,2)),(4,F(1,4),F(1,2)),(5,F(1,4),F(1,2))],2,None),
        ([(2,F(0),F(1,4)),(2,F(1,2),F(1,4)),(4,F(0),F(1,2)),
          (5,F(0),F(1,2))],4,5),
    ]
    checked = 0
    for rows,cells,first in samples:
        end = 4*len(rows)*lcm(*(2*m for m,_,_ in rows))
        seen = []
        for n in range(1,end+1):
            a = [H(n,rows,z) for z in range(cells)]
            b = [sum(J(n//d,rows,z) for d in range(1,n+1,2) if n%d==0)
                 for z in range(cells)]
            assert a==b
            if len(set(a))>1:
                seen.append(n)
            checked += cells
        assert (seen[0] if seen else None)==first
    rows = samples[1][0]
    shell = [H(2,rows,z) for z in range(3)]
    assert shell==[-2,1,1]
    assert sum(abs(v) for v in shell)*F(1,6)==F(2,3)
    assert sum(v*v for v in shell)*F(1,3)==2
    return checked


def theta(q,x):
    return mp.jtheta(3,mp.pi*x,q)


def double_identity():
    cases = 0
    for q in map(mp.mpf,['.1','.25','.5','.72']):
        C = theta(q,0)*theta(q,mp.mpf('.5'))/theta(q*q,mp.mpf('.5'))
        for j in range(-15,16):
            x = mp.mpf(j)/17
            a = theta(q,x)*theta(q,x+mp.mpf('.5'))
            b = C*theta(q*q,2*x+mp.mpf('.5'))
            assert abs(a-b)<mp.mpf('1e-68')
            cases += 1
        prod = [theta(q,-mp.mpf(j)/4)*theta(q,mp.mpf('.5')-mp.mpf(j)/4)
                *theta(q*q,-mp.mpf(j)/2) for j in range(4)]
        assert max(prod)-min(prod)<mp.mpf('1e-68')
        # The first group alone, and the second, each varies.
        assert abs(theta(q*q,0)-theta(q*q,mp.mpf('.5')))>mp.mpf('1e-5')
    return cases


def order_three():
    out = []
    for s in map(mp.mpf,['1.8','2.2','2.6']):
        q = mp.exp(-mp.pi*s*s)
        ell3 = mp.mpf('.25')
        # Poisson sum of the one-dimensional row-three masses in each mod-3
        # coset; the common factor s/(3*ell3) cancels.
        cq = mp.exp(-mp.pi*(s/(3*ell3))**2)
        pa = [theta(cq,mp.mpf(j)/3) for j in range(3)]
        qa = [a*theta(q,-mp.mpf(j)/3)*theta(q,mp.mpf('.5')-mp.mpf(j)/3)
              for j,a in enumerate(pa)]
        p,qv = [[v/sum(a) for v in a] for a in [pa,qa]]
        tv = sum(abs(a-b) for a,b in zip(p,qv))/2/q**2
        cs = sum((a-b)**2/b for a,b in zip(p,qv))/q**4
        assert abs(tv-mp.mpf(2)/3)<mp.mpf('1e-6')
        assert abs(cs-2)<mp.mpf('3e-6')
        out.append((mp.nstr(tv,15),mp.nstr(cs,15)))
    return out


if __name__=="__main__":
    mp.dps=85
    print("Exact shell/odd-divisor coefficient checks:",exact_coeffs())
    print("High-precision theta doubling and cancellation:",double_identity())
    print("Scaled TV and chi-square, order-three case:",order_three())
    print("PASS")
