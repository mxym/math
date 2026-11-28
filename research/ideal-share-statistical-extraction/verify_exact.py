#!/usr/bin/env python3
# Exact finite checks of the constructions and inequality, not theorem proofs.
from fractions import Fraction as Q
from itertools import combinations, product
from random import Random


def tv(p, r):
    return sum(abs(a-b) for a, b in zip(p, r)) / 2


def translate(p, m):
    return p[-m:] + p[:-m] if m else p


def projection_checks():
    count = 0
    for q in range(2, 13):
        u = [Q(1, q)]*q
        for eps in [Q(0), Q(1, 1000*q), Q(1, 16*(q-1)), Q(1, 8*(q-1))]:
            for a, m0 in product(range(q), repeat=2):
                law = []
                for m in range(q):
                    p = [(1-2*eps)*v for v in u]
                    p[a] += eps
                    p[(a+m0-m) % q] += eps
                    assert min(p) >= 0 and sum(p) == 1
                    law.append(p)
                for m1, m2 in combinations(range(q), 2):
                    assert tv(law[m1], law[m2]) == eps
                    assert tv(translate(law[m1], m1), translate(law[m2], m2)) == eps
                assert tv(law[m0], u) == 2*(1-Q(1, q))*eps
                count += 1
    return count


def grouping_checks():
    rng = Random(449103)
    total = 0
    for q in range(2, 11):
        u = [Q(1, q)]*q
        for _ in range(1200):
            masses = [rng.randrange(20) for _ in range(q)]
            masses[0] += 1
            p = [Q(v, sum(masses)) for v in masses]
            m = [Q(0)]*q
            for y in range(q):
                m[rng.randrange(q)] += p[y]
            assert tv(p, u) <= tv(m, u)
            total += 1
    # Negative control: an exact decoder alone does not imply the same
    # uniformity comparison with a strictly larger share alphabet.
    assert tv([Q(1, 2), Q(1, 2), Q(0)], [Q(1, 3)]*3) == Q(1, 3)
    return total


def rectangle_checks():
    total = 0
    for q in range(2, 6):
        domain = list(product(range(q), repeat=q))
        for i, j in combinations(range(q), 2):
            w, r = Q(1, 4*q), 1-Q(1, q)
            residual = [[Q(1, q)]*q for _ in range(q)]
            corners = {}
            for a, b in product((0, 1), repeat=2):
                xx = [2 % q]*q
                xx[i], xx[j] = a, b
                x = tuple(xx)
                corners[x] = 1 if a == b else -1
                for s,v in enumerate(x):
                    residual[s][v] -= w
            assert all(min(row) >= 0 and sum(row) == r for row in residual)
            base = {}
            for x in domain:
                mass = r
                for s,v in enumerate(x):
                    mass *= residual[s][v]/r
                base[x] = mass + (w if x in corners else 0)
            two = [{x: base[x]+sign*w*corners.get(x,0) for x in domain}
                   for sign in (-1, 1)]
            report = []
            for p in two:
                assert min(p.values()) >= 0 and sum(p.values()) == 1
                margins = [[Q(0)]*q for _ in range(q)]
                for x,v in p.items():
                    for s,z in enumerate(x):
                        margins[s][z] += v
                assert all(m == [Q(1,q)]*q for m in margins)
                report.append(sum(v for x,v in p.items() if x[i] == 0 and x[j] == 0))
            assert report[1]-report[0] == 2*w
            assert max(abs(v-Q(1,q)) for v in report) >= w
            total += 1
    return total


print(f"Exact projection witnesses (q=2..12, both marginal families): {projection_checks()}")
print(f"Decoder-group total-variation comparisons and larger-alphabet negative control: {grouping_checks()} + 1")
print(f"Exact full-key-space rectangle switches, q=2..5: {rectangle_checks()}")
