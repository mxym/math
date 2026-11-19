#!/usr/bin/env python3
"""Exact finite consistency checks for the analytic proof, not a dimension threshold."""
from fractions import Fraction as F
from math import comb, factorial, prod
from itertools import product


def check(ok, msg):
    if not ok:
        raise ArithmeticError(msg)


def rising(x,n):
    return prod(x+k for k in range(n))


def normalize(a):
    return F(factorial(2*a),4**a*factorial(a)*factorial(a-1))


def sphere_cap(a):
    # H(sqrt(x))=1/2-c_a*sum_j (-1)^j binom(a-1,j) x^(j+1/2)/(2j+1).
    # If X~Beta(a,a) then E[X^s]=(a)_a/(a+s)_a for integer a.
    c = normalize(a)
    tail = sum((-1)**j * comb(a-1,j)*F(rising(a,a),rising(a+j+F(1,2),a))/(2*j+1)
               for j in range(a))
    return 3*(F(1,2)-c*tail)


def sphere_cdf(a):
    # Instead integrate Beta(a,a)'s polynomial lower CDF against Y~Beta(1/2,a).
    inv_beta = F(factorial(2*a-1),factorial(a-1)**2)
    e = sum((-1)**h*comb(a-1,h)*F(rising(F(1,2),a+h),rising(F(1,2)+a,a+h))/(a+h)
            for h in range(a))
    return F(3,2)*inv_beta*e


def main():
    ps = []
    for a in range(1,41):
        s = sphere_cap(a)
        check(0<s<1 and s==sphere_cdf(a), ("sphere",a))
        ps.append(s)
    check(ps[0] == F(1,2), "dimension three")
    print("Independent exact cap and CDF expansions agree for 40 odd dimensions 3..81.")
    print("d=3,5,7:", *ps[:3])

    count=0
    for t in [F(i,51) for i in range(-50,51)]:
        # Differentiate q=N/D directly in A at A=B=1.
        n=1-t**2; d=2+2*t; n1=2-2*t**2; d1=2+2*t
        check(n/d==(1-t)/2 and n1/n-d1/d==1, ("q derivative",t))
        x=(1+t)/2
        check(F(16,27)-4*x*(1-x)**2==4*(F(4,3)-x)*(x-F(1,3))**2,("saddle",t))
        count+=1
    print("Equal-radius logarithmic derivative and exact saddle factorization:",count,"rational directions.")

    count=0
    for t,A,B in product([F(-i,16) for i in range(1,15)],
                         [F(i,8) for i in range(8,35)],
                         [F(i,8) for i in range(8,35)]):
        r=A*B
        d=A*A+B*B+2*r*t; n=1+r*t
        db=2*r*(1+t)
        check(d-db==(A-B)**2 and d>=db>0, ("balance",t,A,B))
        if n>0:
            check(n*n/d<=n*n/db,("cap",t,A,B))
        check(t*r-1<0,("g derivative",t,r))
        count+=1
    print("Balanced denominator, signed cap upper bound, monotone comparison:",count,"triples.")
    print("PASS (finite identities only; asymptotic estimates and global optimality are analytic).")


if __name__=="__main__":
    main()
