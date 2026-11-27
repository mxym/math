#!/usr/bin/env python3
"""Exact certificate for balanced binomial collisions for shifts 2..128."""
from math import comb, isqrt, prod
from fractions import Fraction

checks = 0


def check(a):
    global checks
    checks += 1
    if not a:
        raise AssertionError("exact check failed")


def cutoff(d):
    return (128 if d % 6 in (1,5) else 11)*d*d+d


def enclosure(d, u):
    # Rational lower and upper bounds, with common denominator den.
    # This is (w_0 - 4d^4/v^2, w_0 + 4d^4/v^2).
    V = 2*u-2*d+1
    Z = 24*u*u-12*(5*d-3)*u+(d-1)*(25*d+1)
    C = V*(Z*V-2*(d*d-1))
    E = 384*d**4
    return C-E, C+E, 24*V*V


def rootfloor(u, w):
    # Largest integer k >= 0 with (u+k)(k+1) <= w, or -1 below k=0.
    if w < u:
        return -1
    return (isqrt((u-1)**2+4*w)-(u+1))//2


def target(d, u):
    return prod(range(u-2*d+1,u+1))


def product(d,u,w):
    return prod(w+i*(u-1)-i*i for i in range(d))


def certify(d):
    tried, possible, solutions = 0, 0, []
    for u in range(2*d, cutoff(d)):
        tried += 1
        if u < 3*d:
            rhs = target(d,u)
            lo,hi = 0,u
            while hi-lo > 1:
                k = (lo+hi)//2
                if product(d,u,(u+k)*(k+1)) < rhs:
                    lo=k
                else:
                    hi=k
            K = range(hi,min(hi+1,u))
        else:
            L,H,q = enclosure(d,u)
            lo = max(1,rootfloor(u,(L-1)//q)+1)
            hi = min(u-1,rootfloor(u,H//q))
            K = range(lo,hi+1)
        for k in K:
            possible += 1
            if product(d,u,(u+k)*(k+1)) == target(d,u):
                solutions.append((u+k,k,d))
    return tried,possible,solutions


def direct(d, U):
    return [(u+k,k,d) for u in range(2*d,U)
            for k in range(1,u)
            if comb(u+k,k)==comb(u+k-d,k+d)]


def main():
    counts = [0,0]
    for d in range(1,129):
        S0 = [Fraction(2*j+1,2)**2 for j in range(d)]
        S1 = [Fraction(2*j-(d-1),2)**2 for j in range(d)]
        E = -Fraction(5*d*d+1,24)
        D = -Fraction(d*d-1,24)
        check(sum(S0)==Fraction(d*(4*d*d-1),12))
        check(sum(S1)==Fraction(d*(d*d-1),12))
        check(d*E-Fraction(3,2)*sum(S1)==-sum(S0))
        check(2*d*D+sum(S1)==0)
        if d==1:
            continue
        # Test the signed root enclosure using only scaled integer products.
        for u in [3*d,3*d+1,5*d,10*d,20*d,100*d,cutoff(d)-1,cutoff(d),2*cutoff(d)]:
            L,H,q = enclosure(d,u)
            rhs = target(d,u)*q**d
            check(prod(L+q*(i*(u-1)-i*i) for i in range(d))<rhs<
                  prod(H+q*(i*(u-1)-i*i) for i in range(d)))
            if u>=cutoff(d):
                Z = 24*u*u-12*(5*d-3)*u+(d-1)*(25*d+1)
                if d % 6 in (1,5):
                    check(Z % 24 == 0)
                    check((Z-1)*q < 24*L < 24*H < Z*q)
                else:
                    check(Z % 24 != 0)
                    check((Z-1)*q < 24*L < 24*H < (Z+1)*q)
        s,t,sol = certify(d)
        counts[0]+=s
        counts[1]+=t
        check(sol==[])
        if d<=6:
            check(direct(d,6*d)==[])
    check(comb(15,5)==comb(14,6)==3003)
    print(f"Balanced binomials: {checks} exact assertions; "
          f"{counts[0]} u-values and {counts[1]} candidate positions; "
          "no positive collision for shifts 2..128.")


if __name__ == "__main__":
    main()
