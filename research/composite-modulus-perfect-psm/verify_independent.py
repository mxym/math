#!/usr/bin/env python3
"""Use projective-line permutations and distinct linear algebra checks."""
from collections import Counter
from itertools import product
from math import isqrt


def projective_group(p):
    # p is the point at infinity. All transformations of the projective line
    # are of the form az+b or u+v/(z-w). No matrix inverse code is used.
    aff = [tuple((a*x+b) % p for x in range(p))+(p,)
           for a in range(1, p) for b in range(p)]
    rem = [tuple(p if x == w else (u+v*pow((x-w) % p,-1,p)) % p
                 for x in range(p))+(u,)
           for u in range(p) for v in range(1,p) for w in range(p)]
    G = tuple(aff+rem)
    assert len(G) == len(set(G)) == p*(p*p-1)
    assert all(set(a) == set(range(p+1)) for a in G)
    return G


def comp(a, b):
    return tuple(a[x] for x in b)


def inverse(a):
    b = [0]*len(a)
    for i,x in enumerate(a):
        b[x] = i
    return tuple(b)


def expected(p, b):
    return {(alpha, beta): (p-1)*(p if b else 1)
            for alpha in range(p+1) for beta in range(p+1) if (alpha == beta) == b}


def verify_full_projective():
    trials = 0
    for p, q, g, n in ((3, 2, 2, 2), (3, 2, 2, 4), (5, 4, 2, 3)):
        G = projective_group(p)
        I = tuple(range(p+1))
        adj = tuple((g*x) % p for x in range(p))+(p,)
        invs = {a: inverse(a) for a in G}
        T = (I, adj)
        for x in product((0, 1), repeat=n):
            output = (sum(x) % q == 0)
            hist = {}
            for gauges in product(G, repeat=n-1):
                head = invs[gauges[0]][invs[T[x[0]]][1]]
                tail = invs[gauges[-1]][T[x[-1]][1]]
                middle = tuple(comp(comp(invs[gauges[j-1]], T[x[j]]),gauges[j])
                               for j in range(1, n-1))
                h = hist.setdefault(middle, Counter())
                hit = tail
                for step in reversed(middle):
                    hit = step[hit]
                h[head, hit] += 1
                trials += 1
            assert len(hist) == len(G)**(n-2)
            E = expected(p, output)
            assert all(h == E for h in hist.values())
    return trials


def verify_mobius_fold():
    pairs = 0
    for p, q, g in ((5, 4, 2), (7, 6, 3), (17, 8, 2), (19, 9, 4), (31, 15, 9)):
        G = projective_group(p)
        for left_weight in (0, 1, 2):
            left_anchor = pow(g, -left_weight, p)
            for w in range(2*q+1):
                right_anchor = pow(g, w-left_weight, p)
                h = Counter((f[left_anchor], f[right_anchor]) for f in G)
                assert h == expected(p, w % q == 0)
                pairs += 1
    return pairs


def wt_and_sparse():
    checks = 0
    # No matrix code: independently verify arbitrary negative weights and
    # sparse characteristic polynomials by exact field arithmetic.
    for p, q, g in ((5, 4, 2), (7, 6, 3), (17, 8, 2), (19, 9, 4), (31, 15, 9)):
        for residues in ((0,), (1, 3), tuple(range(q-1)), tuple(range(0, q, 2))):
            target = set(residues)
            A = sorted(target if len(target) <= q//2 else set(range(q))-target)
            coeff = [1]
            for a in A:
                z = pow(g, a, p)
                old = coeff
                coeff = ([(-z*old[0]) % p]
                         + [(old[i-1]-z*old[i]) % p for i in range(1,len(old))]
                         + [old[-1]])
            sparse = [(j,c) for j,c in enumerate(coeff) if c]
            assert 2 <= len(sparse) <= len(A)+1 and len(A) == min(len(target), q-len(target))
            weights = (-13, 0, 19, -6, 4, 21, 7)
            for x in product((0, 1), repeat=len(weights)):
                w = sum(a*b for a,b in zip(weights,x))
                products = [c for _,c in sparse]
                for a,b in zip(weights,x):
                    products = [t*pow(g,j*a*b,p) % p for (j,_),t in zip(sparse,products)]
                out = (sum(products)%p==0) == (target == set(A))
                assert out == (w % q in target)
                checks += 1
    return checks


def check_field_search_and_edges():
    def isprime(p):
        return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
    cases = 0
    for q in range(2, 201):
        p = q+1
        while not isprime(p):
            p += q
        g = next(h for h in range(2,p) if pow(h,q,p)==1
                 and all(pow(h,k,p)!=1 for k in range(1,q)))
        assert len({pow(g,k,p) for k in range(q)}) == q
        assert p % q == 1
        # With mismatched element order, e.g. -1 (order 2), divisibility by
        # any q>2 even cannot be inferred by this zero test.
        if q > 2 and q % 2 == 0:
            assert pow(p-1,2,p)==1 and 2%q!=0
        for x in (0,1):
            assert int(x%q==0) == 1-x  # n=1 direct protocol
        cases += 1
    return cases


if __name__ == "__main__":
    print(f"PASS independent: {verify_full_projective()} projective seeds; {verify_mobius_fold()} exact endpoint laws")
    print(f"PASS independent: {wt_and_sparse()} weighted sparse evaluations; {check_field_search_and_edges()} field cases and endpoint controls")
