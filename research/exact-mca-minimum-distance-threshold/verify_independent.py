#!/usr/bin/env python3
"""Independent finite-field span tests and exact rational gap inequalities."""
from fractions import Fraction as Q
from itertools import combinations
from math import prod


def reduce(v, basis, p):
    v = list(v)
    for pivot, b in basis:
        c = v[pivot]
        if c:
            v = [(x-c*y) % p for x,y in zip(v,b)]
    return tuple(v)


def make_basis(cols, p):
    b = []
    for c in cols:
        v = reduce(c,b,p)
        pivot = next((i for i, x in enumerate(v) if x), None)
        if pivot is not None:
            norm = pow(v[pivot], -1, p)
            b.append((pivot, tuple(norm*x % p for x in v)))
    return b


def ev(polys, x, p):
    return tuple(sum(pow(x,j,p)*a for j,a in enumerate(coeff)) % p for coeff in polys)


def make_fiber_case(p, d, r, n):
    h = d+2
    R = h*r-1
    parts = {}
    for a in range(1,p):
        parts.setdefault(pow(a,r,p), []).append(a)
    assert all(len(w)==r for w in parts.values())
    b, rem = divmod(n,r)
    A = list(parts)[:b]
    D = sum((parts[x] for x in A), [])
    if rem:
        D += list(parts.values())[b][:rem]
    cols = []
    for a in D:
        inv = pow(prod(a-b for b in D if b!=a) % p,-1,p)
        cols.append(tuple(inv*pow(a,i,p) % p for i in range(R)))
    assert len(make_basis(cols,p)) == R
    Y = [tuple(int(i==r-1+j*r) for i in range(R)) for j in range(d+1)]

    # Eliminate each supported column span, then test the entire quotient polynomial.
    # This method never uses the locator identity, planted error weights, or distances.
    all_close, all_bad, witnesses = set(),set(),set()
    checked = 0
    for t in range(r+1):
        for E in combinations(range(n),t):
            basis = make_basis([cols[i] for i in E],p)
            assert len(basis)==t
            quotient = [reduce(v,basis,p) for v in Y]
            polys = tuple(row for row in zip(*quotient) if any(row))
            for x in range(p):
                if not any(ev(polys,x,p)):
                    all_close.add(x)
                    if polys:
                        all_bad.add(x)
                        witnesses.add((x,frozenset(D[i] for i in E)))
            checked += 1
    assert all_close == all_bad == set(A), (p,d,r,n,all_close,all_bad,A)
    assert witnesses == {(x,frozenset(parts[x])) for x in A}
    return checked, len(all_bad)


def gap_checks():
    k = 0
    for d in range(1,21):
        h=d+2
        for r in range(1,11):
            for n in (h*r, h*r+1, 2*h*r, 2*h*r+1, 7*h*r+2, 2*(h-1)*r*r+2*h*r):
                y=Q(r,n)
                z=1-h*y
                assert (1-y)**h>z
                assert 2*y<h*y
                if n>=2*h*r:
                    lo=Q(h-1,2)*y*y
                    hi=2*(h-1)*y*y
                    assert 0<1-y-hi<1-y-lo
                    # Raising to an integer power tests the bounds without floating points.
                    assert (1-y-hi)**h<=z<=(1-y-lo)**h
                    assert d*y/hi>=1/(4*y) and d*y/lo<=2/y
                    assert (1-h*y/2)**h < z
                k += 1
    return k


def main():
    cases = ((5,1,1,3),(5,2,1,4),(13,1,2,9),(17,2,2,11),
             (19,1,3,13),(19,2,3,16),(23,3,1,22),(31,2,3,27))
    t = m = 0
    for p,d,r,n in cases:
        checked, bad = make_fiber_case(p,d,r,n)
        assert bad == n//r
        t += checked
        m += bad
    print(f'Syndrome quotient enumeration: {len(cases)} ordinary RS cases, {t} erasure sets, {m} exact seed/support pairs')
    print(f'Rational generalized-Johnson checks: {gap_checks()} parameter rows')


if __name__ == '__main__':
    main()
