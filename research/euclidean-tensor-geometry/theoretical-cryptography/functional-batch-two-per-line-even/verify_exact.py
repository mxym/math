#!/usr/bin/env python3
"""Direct PG(1,q) polynomial determinant and Legendre valuation."""
from collections import defaultdict
from math import factorial
from random import Random


def val2(n):
    assert n
    return (abs(n) & -abs(n)).bit_length()-1


def times_linear(p, lin):
    out = defaultdict(int)
    for c, v in p.items():
        for i, z in lin:
            cc = list(c)
            cc[i] += 1
            out[tuple(cc)] += v*z
    return dict((c,v) for c,v in out.items() if v)


def quotient_polys(q):
    # In dimension two: different projective lines meet only at zero;
    # a translate of one line meets each other line in exactly one point.
    n = q+1
    X = tuple((i, 1) for i in range(n))
    B = [[() for j in range(n+1)] for i in range(n+1)]
    for i in range(n):
        B[0][i+1] = ((i, q-1),)
        B[i+1][0] = ((i, 1),)
        B[i+1][i+1] = ((i,q-2),) if q>2 else ()
        for j in range(n):
            if j!=i:
                B[i+1][j+1] = tuple((k,1) for k in range(n) if k not in (i,j))
    out = defaultdict(int)

    def leibniz(i, cols, sign, prod):
        if not cols:
            for c, v in prod.items():
                out[c] += sign*v
            return
        for parity, j in enumerate(cols):
            if B[i][j]:
                leibniz(i+1,cols[:parity]+cols[parity+1:],
                        sign*(-1)**parity,times_linear(prod,B[i][j]))

    one = {(0,)*n:1}
    leibniz(0,tuple(range(n+1)),1,one)
    direct = {c:v for c,v in out.items() if v}
    fact = times_linear(one,X)
    for h in range(n):
        fact = times_linear(fact,tuple((i, 1-q if i==h else 1) for i in range(n)))
    assert direct == {c: (-1)**n*(q-1)*v for c,v in fact.items()}
    return fact


def run():
    rng = Random(313)
    checks = 0
    for a in range(2,7):
        q = 1<<a
        for s in range(1,7):
            N = (q**s-1)//(q-1)
            # Legendre v2(n!) = n - popcount(n), independent of factor grouping.
            js = range(1,N+1) if N<=1024 else sorted(
                {1,2,q,q+1,N-q,N-1,N}|{rng.randint(1,N) for _ in range(120)})
            for j in js:
                delta = (a-1)*j + N.bit_count() - (N-j).bit_count()
                assert delta>=a
                if j in (1,2):
                    assert delta==a
                checks += 1
    print(f"EXACT: {checks} falling-factorial Legendre checks, including sharp j=1/2")
    coeff = quotient_polys(4)
    assert len(coeff)==210
    for c,z in coeff.items():
        m=factorial(6)
        for d in c:
            m//=factorial(d)
        assert val2(z)==val2(m) and (z+3*m)%(8<<val2(m))==0
    print("EXACT: all 210 PG(1,4) coefficients, independent Leibniz/factorization exact match")
    assert quotient_polys(2).get((3,1,0),0)==0
    print("EXACT: formal PG(1,2) x^3 y zero-coefficient negative control PASS")


if __name__=="__main__":
    run()
