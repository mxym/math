#!/usr/bin/env python3
"""Small synthetic checks of the ideal-modulus theta mixture. Python 3 only."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import exp, pi, prod, sqrt


class Chain:
    def __init__(self, name, q, e, add, mul, uniformizer):
        self.name, self.q, self.e, self.size = name, q, e, q**e
        self.rng = range(self.size)
        self.add = [[add(x, y) for y in self.rng] for x in self.rng]
        self.mul = [[mul(x, y) for y in self.rng] for x in self.rng]
        p = 1
        valuations = [-1] * self.size
        for k in range(e + 1):
            ideal = set(self.mul[p])
            assert len(ideal) == q**(e - k)
            for x in ideal:
                valuations[x] = k
            p = self.mul[uniformizer][p]
        assert min(valuations) == 0 and valuations[0] == e
        self.v = valuations

    def depth(self, v):
        return self.e - min(map(self.v.__getitem__, v))


def zp(p, e):
    s = p**e
    return Chain(f"Z/{s}", p, e, lambda x, y: (x + y) % s,
                 lambda x, y: x*y % s, p % s)


def f4mul(x, y):
    z = ((x if y & 1 else 0) ^ (x << 1 if y & 2 else 0))
    return z ^ 7 if z & 4 else z


def f4t2():
    def mul(x, y):
        return f4mul(x & 3, y & 3) ^ (
            (f4mul(x >> 2, y & 3) ^ f4mul(x & 3, y >> 2)) << 2)
    return Chain("F4[t]/t^2", 4, 2, lambda x, y: x ^ y, mul, 4)


def zi4():
    def add(x, y):
        a, b, c, d = x % 4, x // 4, y % 4, y // 4
        return (a + c) % 4 + 4*((b + d) % 4)
    def mul(x, y):
        a, b, c, d = x % 4, x // 4, y % 4, y // 4
        return (a*c - b*d) % 4 + 4*((a*d + b*c) % 4)
    return Chain("Z[i]/4", 2, 4, add, mul, 5)


def matrix_image(S, columns, m):
    image = {(0,) * m}
    for col in columns:
        multiples = {tuple(S.mul[c][v] for v in col) for c in S.rng}
        image = {tuple(S.add[a][b] for a, b in zip(x, y))
                 for x in image for y in multiples}
    return image


def rank_prob(m, r, q, j):
    return F(1, q**(m*r)) * prod(
        F((q**m - q**i)*(q**r - q**i), q**j - q**i)
        for i in range(j))


@lru_cache(None)
def iid_factor(m, r, q, e):
    if e == 0 or r == 0:
        return F(1)
    assert sum(rank_prob(m, r, q, j) for j in range(r + 1)) == 1
    return sum(rank_prob(m, r, q, j) * F(1, q**(r-j)) *
               iid_factor(m-j, r-j, q, e-1) for j in range(r + 1))


@lru_cache(None)
def killed_count_mean(m, r, q, e, k):
    if k == 0 or r == 0:
        return F(1)
    return sum(rank_prob(m, r, q, j) * q**(j*k) *
               killed_count_mean(m-j, r-j, q, e-1, min(k, e-1))
               for j in range(r+1))


def tails_to_weights(w):
    return tuple(a-b for a, b in zip(w, w[1:]))


def sur_tails(m, r, q, e):
    c = (1 - F(1, q**r)) / (1 - F(1, q**m))
    return (F(1),) + tuple(c / q**((m-r)*k) for k in range(1, e+1)) + (F(0),)


def check_local(S, m, r):
    q, e = S.q, S.e
    points = tuple(product(S.rng, repeat=m))
    n_iid = len(points)**r
    n_sur = 0
    sum_images = [0, 0]
    counts = (Counter(), Counter())
    depth_count = Counter(map(S.depth, points))
    assert depth_count == {0: 1} | {
        k: q**(m*k)-q**(m*(k-1)) for k in range(1, e+1)}
    for cols in product(points, repeat=r):
        img = matrix_image(S, cols, m)
        counts[0].update(img)
        sum_images[0] += len(img)
        if len(img) == q**(e*r):
            n_sur += 1
            counts[1].update(img)
            sum_images[1] += len(img)
    assert F(n_sur, n_iid) == prod(1-F(1, q**j) for j in range(m-r+1, m+1))
    all_w, all_weights = [], []
    for i, nmat in enumerate((n_iid, n_sur)):
        table = {}
        for x in points:
            k = S.depth(x)
            px = F(counts[i][x], nmat)
            if k in table:
                assert table[k] == px
            table[k] = px
        w = tuple(table[k] for k in range(e+1)) + (F(0),)
        weights = tails_to_weights(w)
        assert w[0] == 1 and min(weights) >= 0 and sum(weights) == 1
        for x in points:
            assert sum(weights[S.depth(x):]) == F(counts[i][x], nmat)
        assert sum(weights[h]*q**(m*h) for h in range(e+1)) == F(sum_images[i], nmat)
        all_w.append(w)
        all_weights.append(weights)
    assert all_w[1] == sur_tails(m, r, q, e)
    for k in range(1, e+1):
        diff = killed_count_mean(m, r, q, e, k) - killed_count_mean(m, r, q, e, k-1)
        assert all_w[0][k] == diff / (q**(m*k)-q**(m*(k-1)))
    assert all(a <= b for a, b in zip(*all_w))
    assert F(sum_images[0], n_iid*q**(e*r)) == iid_factor(m, r, q, e)
    tilt = [all_weights[1][h] * F(q**(m*h), q**(e*r)) for h in range(e+1)]
    assert sum(tilt) == 1
    for j in range(1, e+1):
        c = (1 - F(1, q**(m-r))) / (1 - F(1, q**m))
        assert sum(tilt[:e-j+1]) == c/q**(r*j)
    print(f"PASS {S.name}, {m}x{r}: {n_iid} matrices, {len(points)} points,"
          f" image fraction {iid_factor(m,r,q,e)}")
    return all_weights


def check_mixed(integer_factors, weights_by_factor):
    n = prod(integer_factors)
    assert n == 12
    pairs = tuple(product(range(n), repeat=2))
    counts = [Counter(), Counter()]
    total = [len(pairs), 0]
    image_sum = [0, 0]
    for a, b in pairs:
        image = {(k*a % n, k*b % n) for k in range(n)}
        counts[0].update(image)
        image_sum[0] += len(image)
        if len(image) == n:
            counts[1].update(image)
            image_sum[1] += len(image)
            total[1] += 1
    nchecks = 0
    for kind in range(2):
        divisors = {}
        for h4, h3 in product(range(3), range(2)):
            divisors[2**h4 * 3**h3] = weights_by_factor[0][kind][h4] * weights_by_factor[1][kind][h3]
        assert sum(divisors.values()) == 1
        assert sum(p * div**2 for div, p in divisors.items()) == F(image_sum[kind], total[kind])
        # Pointwise finite positive-mixture identity on a nonsymmetric translated
        # box, with a nonradial nonnegative test independent of the proof.
        lhs = rhs = F(0)
        for a, b in product(range(-13, 10), range(-8, 14)):
            pa = F(counts[kind][(a % n, b % n)], total[kind])
            pb = sum(p for div, p in divisors.items()
                     if a % (n//div) == 0 and b % (n//div) == 0)
            assert pa == pb
            f = 1 + (3*a - 2*b + 1)**2
            lhs += f*pa
            rhs += f*pb
            nchecks += 1
        assert lhs == rhs
    print(f"PASS mixed Z/12: {len(pairs)} matrices, {nchecks} lifted point comparisons")


def rank_one_iid_tails(m, q, e):
    # The random-content formula is not needed for the proof.
    sw = sur_tails(m, 1, q, e)
    return tuple(sw[k]*(1-F(1, q**(m*(e-k+1)))) if 1 <= k <= e else sw[k]
                 for k in range(e+2))


def finite_illustration():
    exp_tests = 0
    for factors in ((2,), (2, 3), (2, 3, 5)):
        output = []
        for e in (2, 5, 10, 20):
            modulus = prod(q**e for q in factors)
            s = sqrt(modulus)
            values = []
            for kind in ("sur", "iid"):
                local = [tails_to_weights(sur_tails(2, 1, q, e) if kind=="sur"
                    else rank_one_iid_tails(2, q, e)) for q in factors]
                norm = prod(sum(p*q**(2*h) for h, p in enumerate(weights))
                         for q, weights in zip(factors, local))
                ref = (F(modulus) if kind=="sur"
                       else modulus*prod(iid_factor(2, 1, q, e) for q in factors))
                assert norm == ref
                val = 0.0
                for hs in product(range(e+1), repeat=len(factors)):
                    b = prod(q**h for q, h in zip(factors, hs))
                    prob = float(prod(weights[h] for weights, h in zip(local, hs))*b*b/norm)
                    x = b/s
                    if x <= 1:
                        t = 2*sum(exp(-pi*(j/x)**2) for j in range(1, 10))
                        f = t*(2+t)/(x*x)
                    else:
                        t = 2*sum(exp(-pi*(j*x)**2) for j in range(1, 10))
                        f = (1+t)**2 - 1/(x*x)
                    val += prob*f
                assert 0.0 < val < 2.0
                if e == 20:
                    assert abs(val - 1) < 0.02
                values.append(val)
                exp_tests += 1
            output.append(tuple(round(v, 8) for v in values))
        print(f"PASS normalized Gaussian illustrations for prime set {factors}: {output}")
    print(f"PASS {exp_tests} numerical Gaussian means (illustration only)")


if __name__ == "__main__":
    z4 = check_local(zp(2, 2), 2, 1)
    z3 = check_local(zp(3, 1), 2, 1)
    check_local(zp(2, 3), 2, 1)
    check_local(zp(3, 2), 2, 1)
    check_local(zp(2, 2), 3, 2)
    check_local(zp(2, 1), 4, 3)
    check_local(f4t2(), 2, 1)
    check_local(zi4(), 2, 1)
    check_mixed((4, 3), (z4, z3))
    finite_illustration()
