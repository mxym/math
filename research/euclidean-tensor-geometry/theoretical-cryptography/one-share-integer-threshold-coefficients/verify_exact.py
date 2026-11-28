#!/usr/bin/env python3
"""Check literal moment rows, shift basis, finite views, and normalization."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, factorial, lcm, prod


def table(n, k):
    return {
        omitted: tuple(prod(j-u for u in omitted) for j in range(n))
        for omitted in combinations(range(n), k)
    }


def prime_valuation_lcm(n, k):
    out = 1
    for p in range(2, n):
        if any(p % j == 0 for j in range(2, p)):
            continue
        power = p
        while power < n:
            out *= p**min(k, (n-1)//power)
            power *= p
    return out


def basis(n, k):
    return [
        tuple((-1)**(k+1-j+b)*comb(k+1, j-b) if 0 <= j-b <= k+1 else 0
              for j in range(n))
        for b in range(n-k-1)
    ]


def moments(x, k):
    return tuple(sum(j**a*v for j, v in enumerate(x)) for a in range(k+1))


def hvec(n, omitted, L):
    return tuple(L//prod(j-u for u in omitted if u != j) if j in omitted else 0
                 for j in range(n))


def integral_coords(vec, rows):
    v = list(vec)
    cs = []
    for i, row in enumerate(rows):
        assert abs(row[i]) == 1
        x = v[i]*row[i]
        cs.append(x)
        v = [a-x*b for a, b in zip(v,row)]
    assert not any(v)
    return cs


def main():
    family = formulas = shifts = 0
    for n in range(3, 12):
        for k in range(1, n-1):
            family += 1
            t = n-k
            tab = table(n,k)
            coeffs = [abs(v) for row in tab.values() for v in row if v]
            B, L = max(coeffs), lcm(*coeffs)
            assert B == factorial(n-1)//factorial(t-1)
            assert L == prime_valuation_lcm(n,k)
            assert L % lcm(*range(1,t+1)) == 0
            if k == 1:
                assert (B,L) == (t,lcm(*range(1,t+1)))
            rows = basis(n,k)
            assert all(moments(row,k) == (0,)*(k+1) for row in rows)
            O0 = tuple(range(k+1))
            mu0 = hvec(n,O0,L)
            for O, row in tab.items():
                assert set(O) == {j for j in range(n) if not row[j]}
                assert sum(a*b for a,b in zip(row,mu0)) == L
                assert all(sum(a*b for a,b in zip(row,v)) == 0 for v in rows)
                formulas += 1
            for O in combinations(range(n),k+1):
                assert all(L % prod(j-u for u in O if u!=j) == 0 for j in O)
                v = hvec(n,O,L)
                assert moments(v,k) == (0,)*k+(L,)
                assert max(map(abs,v)) <= L
                cs = integral_coords([a-b for a,b in zip(v,mu0)],rows)
                assert max(map(abs,cs)) <= 2*L*comb(n-1,k+1)
                shifts += 1

    finite = 0
    for n,t,H in [(3,2,8),(4,3,16),(5,3,16)]:
        k=n-t
        tab=table(n,k)
        L=lcm(*[abs(v) for row in tab.values() for v in row if v])
        rows=basis(n,k)
        mu=hvec(n,tuple(range(k+1)),L)
        choices=[tuple(sum(u[j]*b for u,b in zip(rows,cs)) for j in range(n))
                 for cs in product(range(H),repeat=t-1)]
        for U in combinations(range(n),t-1):
            hist=[]
            for c in (-1,0,1):
                p=Counter(tuple(c*mu[j]+x[j] for j in U) for x in choices)
                assert sum(p.values()) == H**(t-1)
                hist.append(p)
            for c0,c1 in combinations(range(3),2):
                px,py=hist[c0],hist[c1]
                tv=Fraction(sum(abs(px[a]-py[a]) for a in px.keys()|py.keys()),
                            2*H**(t-1))
                O=tuple(j for j in range(n) if j not in U)
                z=[(c0-c1)*(a-b) for a,b in zip(hvec(n,O,L),mu)]
                cs=integral_coords(z,rows)
                tvbox=1-prod(Fraction(max(0,H-abs(c)),H) for c in cs)
                assert tv <= tvbox <= Fraction(sum(map(abs,cs)),H)
                finite += 1

    # Negative control: the n=3,t=2 table requires even secret differences.
    # Two shares sum to zero with the third; moment 1 recovers the secret.
    # The view at label 1 determines the parity of the secret, since
    # s=x_1+2*x_2. Enumerate two full-reconstruction integer cosets.
    A0={-2*x for x in range(-15,16)}
    A1={1-2*x for x in range(-15,16)}
    assert not A0&A1

    print(f"exact: {family} moment tables, {formulas} reconstructors, {shifts} local shifts PASS")
    print(f"exact: {finite} joint view TV checks and off-lattice negative control PASS")


if __name__ == "__main__":
    main()
