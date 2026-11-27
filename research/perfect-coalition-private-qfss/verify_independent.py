#!/usr/bin/env python3
"""Exact rational rounding, calibration, tail, and median checks."""
from fractions import Fraction as F
from math import comb
from statistics import median


def floor(x):
    return x.numerator // x.denominator


def good_table(J,M,B,P):
    margin = F(1,M)
    for p in P:
        z = B*p+F(J,M)
        s = z-floor(z)
        if min(s,1-s) <= margin:
            return False
    return True


def code_estimate_set(P,M,B,J):
    # Compute both extreme empirical roundings. By monotonicity they bracket any
    # outcome within the allowed error, including clipping of empirical means.
    eps = F(1,2*B*M)
    for p in P:
        y = F(J,M)
        b = floor(B*p+y)
        lo,hi = max(0,p-eps), min(1,p+eps)
        assert 0 <= b <= B and abs(F(b,B)-p)<F(1,B)
        yield floor(B*lo+y) == b == floor(B*hi+y)


def gaussian_constant(xs,ys,q):
    m = [[pow(x,j,q) for j in range(len(xs))] + [y] for x,y in zip(xs,ys)]
    for j in range(len(xs)):
        k=next(k for k in range(j,len(xs)) if m[k][j])
        m[j],m[k]=m[k],m[j]
        m[j]=[z*pow(m[j][j],-1,q)%q for z in m[j]]
        for k in range(len(xs)):
            if k!=j:
                m[k]=[(a-m[k][j]*b)%q for a,b in zip(m[k],m[j])]
    return m[0][-1]


def end_to_end():
    from itertools import product
    from math import prod
    B,M,q=4,64,7
    P=(F(1,2), F(16,25), F(49,50), F(1,50))
    eps=F(1,2*B*M)
    xs=list(range(1,6))
    records=list(product((0,1),repeat=2))
    good_decodings=0
    nonidentical=0
    for z in records:
        zi=records.index(z)
        points=[((z[0]+x+3*x*x)%q,(z[1]+2*x+5*x*x)%q) for x in xs]
        for J in range(M):
            U=F(J,M)
            local=[tuple(floor(B*max(0,min(1,p+eps*(-1)**(i+j)))+U)
                         for j,p in enumerate(P)) for i in range(len(xs))]
            answers=[sum(b*prod(v if bit else 1-v for v,bit in zip(V,w))
                         for b,w in zip(tab,records))%q for tab,V in zip(local,points)]
            out=gaussian_constant(xs,answers,q)
            if good_table(J,M,B,P):
                assert all(t == local[0] for t in local)
                assert out==floor(B*P[zi]+U)
                good_decodings+=1
            if len(set(local))>1:
                nonidentical+=1
    assert nonidentical  # true local estimates can quantize to unequal tables
    return good_decodings, nonidentical


def main():
    # Rational Born data from |psi>=(3/5,4/5) and a |0> outcome:
    # I, X, H, HZ (plus optional invalid zero/midpoint/extreme controls).
    a,b = F(3,5),F(4,5)
    born = (a*a,b*b,(a+b)**2/2,(a-b)**2/2)
    assert born == (F(9,25),F(16,25),F(49,50),F(1,50))
    cases = offsets = forced = 0
    for L in range(7):
        D=2**L
        for B in (1,2,3,7):
            M=16*D
            common = (F(0),F(1),F(1,2),F(1,3),F(2,3),F(1,M)) + born
            synthetic = tuple(F((i*i+7*i+11)%(17*D+13),17*D+13) for i in range(D))
            for P in (tuple(common[i%len(common)] for i in range(D)),synthetic):
                count=0
                bad_each=[0]*D
                for J in range(M):
                    isgood=good_table(J,M,B,P)
                    flags = tuple(code_estimate_set(P,M,B,J))
                    for i,p in enumerate(P):
                        z=B*p+F(J,M)
                        if min(z-floor(z),1-(z-floor(z))) <= F(1,M):
                            bad_each[i] += 1
                    if isgood:
                        assert all(flags)
                        forced += sum(flags)
                        count+=1
                assert max(bad_each)<=4
                assert count >= 3*M//4
                offsets += M
                cases += 1
    assert not all(code_estimate_set((F(1,2),),16,2,0))  # boundary negative control

    tails=0
    for lam in range(1,41):
        K=8*(lam+1)+1
        num=sum(comb(K,k)*3**(K-k) for k in range((K+1)//2,K+1))
        den=4**K
        assert num*2**(lam+1)<=den
        for L in range(7):
            for p in (1,2,L+1,2*L+1):
                v=(p-1).bit_length()
                a=L+lam+v+4
                M=16*2**L
                B=7
                Q=2*a*B*B*M*M
                eps=F(1,2*B*M)
                assert 2*Q*eps**2==a
                assert p*2**L * F(2,2**a)<=F(1,2**(lam+3))
                tails+=1

    # Bad rounds may decode to any number. Strict majority of valid values
    # forces the deterministic median into the same interval even at both extremes.
    for K in (3,5,17,65):
        g=(K+1)//2
        for j in range(K-g+1):
            seq=[F(2,5)]*g+[0]*j+[1]*(K-g-j)
            assert median(seq)==F(2,5)
    assert median([F(2,5)]*2+[0]*3)==0  # without strict majority no guarantee
    rows, misses = end_to_end()
    print(f'Independent prime-field integration: {rows} good-offset decodings, {misses} disagreeing local tables only on bad offsets')
    print(f'Dither checks: {cases} rational tables, {offsets} offsets, {forced} forced-agreement cells')
    print(f'Confidence checks: 40 exact binomial tails, {tails} sample bounds; rounding-boundary and median negative controls PASS')


if __name__=='__main__':
    main()
