#!/usr/bin/env python3
"""Exhaustive binary truth tables and rational product comparisons."""
from fractions import Fraction as F
from itertools import combinations
from math import prod


def degree(tt, n):
    a = tt
    for i in range(n):
        selection = sum(1 << j for j in range(1 << n) if not (j >> i) & 1)
        a ^= (a & selection) << (1 << i)
    return max(j.bit_count() for j in range(1 << n) if (a >> j) & 1)


def truth_mass(bits, weights):
    ans = 0
    while bits:
        q = bits & -bits
        ans += weights[q.bit_length()-1]
        bits ^= q
    return ans


def weighted_product(ps):
    def point_weight(x):
        return prod(p.numerator if (x >> j) & 1 else p.denominator-p.numerator
                    for j, p in enumerate(ps))
    return [point_weight(x) for x in range(1 << len(ps))], prod(p.denominator for p in ps)


def cases(n):
    configs = [
        ([F(1,2)]*4, [F(3,8)]*4),              # q>1/2, all ties
        ([F(1,3),F(1,4),F(2,5),F(1,2)], [F(1,4),F(1,8),F(1,5),F(1,2)]),
        ([F(1,3),F(1,5),F(1,2),F(2,5)], [F(1,3),F(1,5),F(1,3),F(2,5)]),
        ([F(1,2)]*4, [F(1,2)]*4),              # no thinning
        ([F(1,2)]*4, [F(0),F(2,7),F(0),F(1,3)]),
    ]
    for initial, final in configs:
        p, q = initial[:n], final[:n]
        w, den = weighted_product(p)
        z, den2 = weighted_product(q)
        ratios = [y/x for x,y in zip(p,q)]
        active = sum(1 << i for i in range(n) if ratios[i]<1)
        zcoords = sum(1 << i for i in range(n) if not q[i])
        exclude = sum(1 << x for x in range(1<<n) if (x & active) != active)
        face = sum(1 << x for x in range(1<<n) if (x & zcoords) == 0)
        terms=[]
        for d in range(n+1):
            v = prod(sorted(ratios)[:d])
            a = den*v.denominator
            b = den2*v.numerator
            if zcoords and d:
                eq = ('zero-face', face)
            elif d>=active.bit_count():
                eq = ('anchor', exclude)
            else:
                allowed = {sum(1 << x for x in range(1<<n) if (x & k)==k)
                           for k in range(1<<n)
                           if k.bit_count()==d and (k & active)==k and
                           prod(ratios[i] for i in range(n) if (k>>i)&1)==v}
                eq = ('monomials', allowed)
            terms.append((a,b,eq))
        yield w,z,terms


def flat_spectral_support(tt, n):
    a = [1-2*((tt >> x)&1) for x in range(1<<n)]
    b = 1
    while b < len(a):
        for start in range(0,len(a),2*b):
            for j in range(start,start+b):
                u,v=a[j],a[j+b]
                a[j],a[j+b]=u+v,u-v
        b*=2
    if len({abs(x) for x in a if x})!=1: return 0
    return sum(1<<i for i,x in enumerate(a) if x)


def main():
    tables = comparisons = mean_eq = compare_eq = flat_checked = 0
    for n in range(1,5):
        configs = list(cases(n))
        masks = [x.bit_count() for x in range(1<<n)]
        means=[]
        for d in range(n+1):
            k=n-d
            cubes={sum(1<<x for x in range(1<<n) if x & ~u == 0)
                   for u in range(1<<n) if u.bit_count()==k}
            flips={sum(1<<(x^((1<<n)-1)) for x in range(1<<n) if (t>>x)&1) for t in cubes}
            means.append((cubes,flips))
        for tt in range(1,1<<(1<<n)):
            d = degree(tt,n)
            rw = 2*truth_mass(tt,masks)
            size = tt.bit_count()
            lo,hi = (n-d)*size,(n+d)*size
            assert lo<=rw<=hi
            assert (rw==lo)==(tt in means[d][0])
            assert (rw==hi)==(tt in means[d][1])
            mean_eq += (rw==lo)+(rw==hi)
            for w,z,terms in configs:
                a,b,(kind,data)=terms[d]
                left,right=a*truth_mass(tt,z),b*truth_mass(tt,w)
                assert left>=right
                if kind=='monomials': expect=tt in data
                else: expect=(tt & data)==0
                assert (left==right)==expect, (n,tt,d,left,right,kind,data)
                comparisons += 1
                compare_eq += left==right
            sf=flat_spectral_support(tt,n)
            if sf and sf.bit_count()>1:
                count=sf.bit_count()
                h=count.bit_length()-1
                assert h % 2 == 0 and count == 1<<h
                assert degree(sf,n) <= n-h//2
                assert 4*truth_mass(sf,masks) > h*count
                flat_checked += 1
            tables += 1
    print(f'{tables} all nonzero binary tables through n=4; {mean_eq} equality checks at mean-weight endpoints')
    print(f'{comparisons} heterogeneous rational comparisons including q>1/2, zero endpoints and ties; {compare_eq} equalities')
    print(f'{flat_checked} positive-entropy flat Walsh spectra, all H<4I')
    # The anchor-zero hypothesis p<=1/2 is necessary: for parity on
    # three bits start p=7/8 and use p'=3/4.
    def parity(p):
        return (1-(1-2*p)**3)/2
    assert parity(F(3,4)) < F(6,7)*parity(F(7,8))
    print('negative control: the binary comparison can fail above 1/2 with anchor zero')
    print('PASS binary degree, mean-rank rigidity and thinning contrasts')


if __name__=='__main__': main()
