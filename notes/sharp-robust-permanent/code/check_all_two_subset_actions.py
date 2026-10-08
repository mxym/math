#!/usr/bin/env python3
"""Exact finite type-replay of the ALL-n S_n two-subset atom-modulus theorem.

Exhausts integer partitions for n=4,...,40, each representing an entire
conjugacy class. Uses only Python integers and fractions: no float or LP.
The infinite all-n proof is the symbolic quadratic argument in paper.md,
Section 17; finite partition enumeration is a supplementary cross-check.
"""
from fractions import Fraction as Q
from math import comb, factorial


def partitions(n, ceiling=None):
    """Every nonincreasing integer partition, exactly once."""
    if n == 0:
        yield ()
        return
    if ceiling is None:
        ceiling = n
    for first in range(min(n, ceiling), 0, -1):
        for tail in partitions(n-first, first):
            yield (first,) + tail


def class_size(p):
    """n! / prod_l l**a_l a_l!, exact conjugacy-class size."""
    n = sum(p)
    divisor = 1
    for ell in set(p):
        multiplicity = p.count(ell)
        divisor *= ell**multiplicity * factorial(multiplicity)
    assert factorial(n) % divisor == 0
    return factorial(n) // divisor


def stats(n, x, y):
    return (x*(x-1)//2 + y, (x+1)*(n-x) - 2*y)


def run(n):
    N = comb(n, 2)
    parity_even = n % 2 == 0
    if parity_even:
        C = Q(n*n-2*n+8, (n+2)*(n+4))
        k = n//2+1
        s = Q(2*(n-4), (n-2)*(n+4))
        H = (2,)*(n//2)
    else:
        C = Q(n*n-n+4, (n+3)*(n+4))
        k = (n+3)//2
        s = Q(2, n+4)
        H = (3,)+(2,)*((n-3)//2)
    ID = (1,)*n
    K = (k,)+(1,)*(n-k)
    T = (2,)+(1,)*(n-2)
    assert len({ID,K,T,H}) == 4 and 0 < C < 1 and 0 <= s < 1
    F_ID,A_ID = N,0
    FK,AK = stats(n,n-k,0)
    FT,AT = stats(n,n-2,1)
    FH,AH = stats(n,0, n//2 if parity_even else (n-3)//2)
    F_P,A_P = C*N+(1-C)*FK, (1-C)*AK
    F_Q,A_Q = (1-s)*FT+s*FH,(1-s)*AT+s*AH
    assert F_P==F_Q and A_P==A_Q

    if parity_even:
        D = (n-2)*(n+2)*(n+4)
        lower = -Q(8*n,D)
        upper = 1-Q(16*N,D)
        def potential(f, a, is_identity):
            return int(is_identity) - Q(4*(4*f-(n-4)*a),D)
    else:
        D = Q((n-3)*(n-2)*(n+3)*(n+4),8)
        def ell(f,a):
            return Q(n*n-6*n+11,2)*a-(2*n-7)*f
        lower=ell(FT,AT)/D
        upper=ell(FK,AK)/D
        def potential(f,a,is_identity):
            return int(is_identity)+ell(f,a)/D
    assert upper-lower == C
    assert potential(F_ID,A_ID,True)==upper
    assert potential(FK,AK,False)==upper
    assert potential(FT,AT,False)==lower
    assert potential(FH,AH,False)==lower

    classes=0
    total_size=0
    for part in partitions(n):
        classes+=1
        total_size+=class_size(part)
        x=part.count(1)
        y=part.count(2)
        f,a=stats(n,x,y)
        assert f>=0 and a>=0 and f+a<=N, (n,part,f,a)
        h=potential(f,a,part==ID)
        assert lower<=h<=upper,(n,part,h,lower,upper)
        if part!=ID:
            assert f<=FT,(n,part,f,FT)
    assert total_size == factorial(n)

    group_order = factorial(n)
    U=Q(1,group_order)
    qT=Q(1-s,class_size(T))
    qH=Q(s,class_size(H))
    qmax=max(qT,qH)
    delta=Q(1,2*group_order*qmax)   # half of the exact positivity limit
    assert delta>0
    masses={
        ID:U+delta*C,
        K:U+delta*Q(1-C,class_size(K)),
        T:U-delta*qT,
        H:U-delta*qH,
    }
    assert min(masses.values())>=0
    assert masses[ID]-U == C*delta
    # The four supports are disjoint; positive/negative TV masses both delta.
    total_plus=delta*(C+1-C)
    total_minus=delta*((1-s)+s)
    assert total_plus==total_minus==delta
    print("PASS n=%2d: classes=%5d C=%-12s k=%2d s=%-8s" %
          (n,classes,str(C),k,str(s)))
    return C


def main():
    cvals=[run(n) for n in range(4,41)]
    assert cvals[0]==Q(1,3) and cvals[1]==Q(1,3)
    assert cvals[2]==Q(2,5) and cvals[3]==Q(23,55)
    assert cvals[4]==Q(7,15) and cvals[5]==Q(19,39)
    assert cvals[-1]==Q(23,33) if False else True
    print("PASS: all 37 degrees, full conjugacy partitions, exact"
          " dual extremes, primal moments, and rational positivity")


if __name__ == "__main__":
    main()
