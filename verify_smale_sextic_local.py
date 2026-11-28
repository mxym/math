#!/usr/bin/env python3
"""Exact arithmetic for the local sextic Smale 5/6 exclusion."""
import json
import sys
from fractions import Fraction as F
from itertools import permutations
from math import prod

Z = (0, 0, 0, 0)
ONE = {Z: F(1)}
W = tuple(map(F, ("5/2", "5", "10", "25")))


def insist(test, detail):
    if not test:
        raise RuntimeError(detail)


def add(a, b, eps=1):
    res = dict(a)
    for key, val in b.items():
        res[key] = res.get(key, F(0)) + eps*val
        if not res[key]:
            del res[key]
    return res


def mul(a, b):
    out = {}
    for t, x in a.items():
        for u, y in b.items():
            s = tuple(v+w for v,w in zip(t,u))
            out[s] = out.get(s, F(0)) + x*y
    return {s:x for s,x in out.items() if x}


def determinant():
    units = [tuple(int(i == j) for i in range(4)) for j in range(4)]
    v = [{t: F(1)} for t in units]
    weighted = [{t: w} for t,w in zip(units,W)]
    # Coordinate vectors for z^k modulo z^5 - 1 - sum_j W[j-1] v_j z^j.
    powers = [[ONE if i==k else {} for i in range(5)] for k in range(5)]
    for k in range(5,9):
        p = list(powers[k-5])
        for j in range(1,5):
            p = [add(b,mul(weighted[j-1],a))
                 for a,b in zip(powers[k-5+j],p)]
        powers.append(p)
    cols = []
    for k in range(5):
        p = list(powers[k])
        for j in range(1,5):
            p = [add(b,mul(v[j-1],a)) for a,b in zip(powers[k+j],p)]
        cols.append(p)
    out = {}
    for order in permutations(range(5)):
        x = ONE
        for i,j in enumerate(order):
            x = mul(x,cols[i][j])
        inversions = sum(order[i]>order[j] for i in range(5) for j in range(i+1,5))
        out = add(out,x,(-1)**inversions)
    return out


def higher_constants(poly):
    sums = {}
    for alpha,c in poly.items():
        k = sum(alpha)
        if k<4:
            continue
        choices = []
        for i in range(4):
            for j in range(i,4):
                left = list(alpha)
                left[i] -= 1
                left[j] -= 1
                if min(left) < 0:
                    continue
                factor = prod((F(n,k-2)/w)**n for n,w in zip(left,W) if n)
                choices.append(factor*F(1,1 if i==j else 2))
        sums[k] = sums.get(k,F(0)) + abs(c)*min(choices)
    return sums


def reciprocal_terms(poly):
    out = []
    for a,c in sorted(poly.items(),reverse=True):
        if a==Z:
            continue
        w=sum((j+1)*n for j,n in enumerate(a))
        insist(w%5==0 and w<=20, ("unexpected weight", a, c))
        d=c*prod(F((4-j)*(-1)**(j+1),5*(j+2))**n for j,n in enumerate(a))
        out.append([list(a),w//5,d.numerator,d.denominator])
    return out


def check_reciprocal_substitution(poly):
    def elementary(values):
        out = [F(1)] + [F(0)]*len(values)
        for i,z in enumerate(values,1):
            for k in range(i,0,-1):
                out[k] += z*out[k-1]
        return out

    terms = reciprocal_terms(poly)
    for w in [(F(1),F(-1,2),F(3,4),F(1,3),F(2,5)),
              (F(1),F(-2,3),F(-2,3),F(1,4),F(-1,4)),
              (F(1),F(1,2),F(2,3),F(2,3),F(3,4))]:
        E = elementary(w)
        substituted = 1 + sum(F(a,b)*prod(E[j+1]**m for j,m in enumerate(alpha))
                              / E[5]**k for alpha,k,a,b in terms)
        direct = F(1)
        for j,wj in enumerate(w):
            e = elementary(w[:j]+w[j+1:])
            direct *= F(6,5)*sum(F((-1)**k,(k+1)*(k+2))*ek/wj**k
                                 for k,ek in enumerate(e))
        insist(substituted==direct, ("reciprocal substitution mismatch", w))


def main():
    R=determinant()
    insist(len(R)==59, ("number of determinant terms",len(R)))
    low={a:c for a,c in R.items() if sum(a)<=3}
    insist(low=={Z:1,(1,0,0,1):30,(0,1,1,0):30,
                 (2,0,1,0):-15,(1,2,0,0):-15,(0,1,0,2):960,(0,0,2,1):810},
           ("constant through cubic part",low))
    C=higher_constants(R)
    target={4:F(60193,2000),5:F(8531299,375000),6:F(420163,2560000),
            7:F(5456361,1562500000),8:F(516989,3240000000)}
    insist(C==target, ("higher coefficients",C))

    a=F(1,7)
    B=1+a/4
    rouche=F(5,4)-F(5,8)*a*B**3-B**4
    insist(rouche==F(19,175616),"Rouche margin")
    insist(F(13,40)*B**3<F(3,8),"root displacement second order")
    insist(F(11,2)*F(3,8)+F(7,16)*B**2<F(13,5),"Taylor remainder in T")
    insist(2+F(11,8)*B**3*a<F(9,4),"maximum of T")
    insist(1+F(4,5)*a+F(13,5)*a*a<F(6,5),"RMS of T")
    logerror=(F(9,4)*F(6,5)*F(2,5))/(2*(1-F(9,70)))
    insist(F(4,5)+F(13,5)*a+logerror<F(9,5),"RMS log error")
    insist(870**2<4*450**2 and 18*25+360==810,"cubic majorant")
    H=18*a+sum(C[k]*a**(k-2) for k in range(4,9))
    insist(H<F(33,10),"total high order bound")
    rho=5*F(37,20)**2*a*a
    bound=2*(15*(2*rho-1)+F(33,10))+(15+F(33,10))**2*F(4,25)*a*a
    insist(bound==F(-3381,2500) and bound<F(-5,4),"final strict bound")

    check_reciprocal_substitution(R)
    if sys.argv[1:]==["--emit-reciprocal-terms"]:
        print(json.dumps(reciprocal_terms(R),separators=(',',':')))
    else:
        print("terms:",len(R),"Rouche margin:",rouche)
        print("higher-majorant constants:", *(C[k] for k in range(4,9)))
        print("final squared-product defect coefficient:",bound)
        print("PASS: local sextic certificate")


if __name__=="__main__":
    main()
