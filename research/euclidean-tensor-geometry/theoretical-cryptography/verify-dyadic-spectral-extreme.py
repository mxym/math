#!/usr/bin/env python3
"""Exact checks for the dyadic Fourier/complex Wishart proof (Python 3 only)."""
from cmath import exp as cexp
from itertools import combinations, permutations, product
from math import factorial, pi, prod
from random import Random


def geometric(d, exponent):
    # All exponents used in the even-order tests below are even. Return
    # the sum in the exact cyclotomic basis 1,z,...,z^(d-1), z^d=-1.
    assert exponent % 2 == 0
    terms = {}
    for j in range(d):
        k = (j*exponent) % (2*d)
        k, sign = (k, 1) if k < d else (k-d, -1)
        terms[k] = terms.get(k, 0)+sign
    return {k: v for k, v in terms.items() if v}


def sum_products(d, u, v, eps1, eps2):
    out = {}
    for s, t in product((1, -1), repeat=2):
        coef = (1 if s == 1 else eps1)*(1 if t == 1 else eps2)
        for k, value in geometric(d, s*u+t*v).items():
            out[k] = out.get(k, 0) + coef*value
    return {k: v for k, v in out.items() if v}


def resonance(freq, d):
    k = len(freq)
    signs = tuple((i, sign) for i in range(k) for sign in (1, -1))
    for relation in combinations_with_multiset(signs, 4):
        net = [0]*k
        for i, sign in relation:
            net[i] += sign
        if any(net) and sum(n*u for n, u in zip(net, freq)) % (2*d) == 0:
            return True
    return False


def combinations_with_multiset(values, k, start=0):
    if k == 0:
        yield ()
        return
    for i in range(start, len(values)):
        for tail in combinations_with_multiset(values, k-1, i):
            yield (values[i],)+tail


def gaussian_int_mul(z, w):
    a, b = z
    c, d = w
    return a*c-b*d, a*d+b*c


def zpoly_mul(p, q, modulus):
    out = {}
    for i, x in p.items():
        for j, y in q.items():
            k = (i+j) % modulus
            a, b = out.get(k, (0, 0))
            c, d = gaussian_int_mul(x, y)
            out[k] = a+c, b+d
    return {k: v for k, v in out.items() if v != (0, 0)}


def check_fourth(freq, d, direction):
    # Pair (a,b) is a+ib. Polynomial P is 2*sum(a_j cos + b_j sin).
    lin = {}
    for u, (a, b) in zip(freq, direction):
        lin[u], lin[2*d-u] = (a, -b), (a, b)
    square = zpoly_mul(lin, lin, 2*d)
    quartic = zpoly_mul(square, square, 2*d)
    assert all(k % 2 == 0 for k in quartic)
    s = [a*a+b*b for a, b in direction]
    assert square.get(0, (0, 0)) == (2*sum(s), 0)
    c4 = quartic.get(0, (0, 0))
    exact_generic = 6*sum(x*x for x in s) + 24*sum(x*y for x, y in combinations(s, 2))
    generic = not resonance(freq, d)
    if generic:
        assert c4 == (exact_generic, 0)
        # Y uses sqrt(2)/2 times P. Therefore 4*kappa_4 = c4 - 12*(sum s)^2.
        assert c4[0]-12*sum(s)**2 == -6*sum(x*x for x in s)
    return generic, c4 != (exact_generic, 0)


def check_fourier():
    rng = Random(20261127)
    grams = tests = generics = exceptions = active = 0
    for d in (4, 8, 16, 32, 64, 128):
        freq = tuple(range(1, d, 2))
        for u, v in product(freq, repeat=2):
            assert sum_products(d, u, v, 1, 1) == ({0: 2*d} if u == v else {})
            assert sum_products(d, u, v, -1, -1) == ({0: -2*d} if u == v else {})
            assert sum_products(d, u, v, 1, -1) == {}
            grams += 3
        for k in range(1, min(4, len(freq))+1):
            groups = list(combinations(freq, k)) if len(freq) <= 16 else [
                tuple(sorted(rng.sample(freq, k))) for _ in range(300)]
            for us in groups:
                direction = tuple((rng.randint(-4, 4), rng.randint(-4, 4)) for _ in us)
                generic, changed = check_fourth(us, d, direction)
                tests += 1
                generics += generic
                exceptions += not generic
                active += changed
    assert generics > 1000 and exceptions > 100 and active > 100
    print(f"PASS {grams} exact odd-root Gram products, {tests} fourth moments"
          f" ({generics} generic and {exceptions} exceptional, {active} active resonances)")


def multiply(p, q):
    # Formal bivariate exact polynomial in E=e^-t and t.
    out = {}
    for (e, i), a in p.items():
        for (f, j), b in q.items():
            z = e+f, i+j
            out[z] = out.get(z, 0)+a*b
    return {k: v for k, v in out.items() if v}


def determinant(A):
    n = len(A)
    result = {}
    for perm in permutations(range(n)):
        inv = sum(x > y for x, y in combinations(perm, 2))
        row = {(0, 0): -1 if inv % 2 else 1}
        for i, j in enumerate(perm):
            row = multiply(row, A[i][j])
        for k, v in row.items():
            result[k] = result.get(k, 0)+v
    return {k: v for k, v in result.items() if v}


def lower_gamma_polynomial(k):
    # int_0^t e^-x x^k dx = k! - E*sum_j (k!/j!)*t^j
    return {(0, 0): factorial(k)} | {
        (1, j): -factorial(k)//factorial(j) for j in range(k+1)}


def check_wishart():
    count = 0
    for p in range(1, 6):
        for q in range(p, 8):
            a = q-p
            det = determinant([[lower_gamma_polynomial(a+i+j) for j in range(p)]
                               for i in range(p)])
            norm = prod(factorial(a+j)*factorial(j) for j in range(p))
            assert det.pop((0, 0)) == norm
            r = max(i for e, i in det if e == 1)
            assert r == p+q-2
            assert -det[1, r]*factorial(p-1)*factorial(q-1) == norm
            count += 1
    print(f"PASS {count} exact Wishart determinant leading tails")


def negacyclic(a, b):
    d = len(a)
    out = [0]*d
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i+j < d:
                out[i+j] += x*y
            else:
                out[i+j-d] -= x*y
    return out


def evaluate(a, z):
    return sum(c*z**i for i, c in enumerate(a))


def check_blocks():
    count = 0
    rng = Random(941)
    for d in (4, 8, 16, 32):
        for m, r in ((1, 2), (2, 3), (3, 3)):
            F = [[tuple(rng.randint(-2, 2) for _ in range(d)) for _ in range(r)] for _ in range(m)]
            x = [tuple(rng.randint(-2, 2) for _ in range(d)) for _ in range(r)]
            fx = [tuple(sum(v) for v in zip(*(negacyclic(f, v) for f, v in zip(row, x)))) for row in F]
            for u in range(1, d, 2):
                z = cexp(1j*pi*u/d)
                for row, t in zip(F, fx):
                    assert abs(evaluate(t, z)-sum(evaluate(f, z)*evaluate(v, z)
                                                  for f, v in zip(row, x))) < 1e-7
                    count += 1
    print(f"PASS {count} synthetic numerical block/multiplication comparisons")


if __name__ == "__main__":
    check_fourier()
    check_wishart()
    check_blocks()
