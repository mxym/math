#!/usr/bin/env python3
"""Full finite dealer laws with arbitrary cyclic group order, not field ranks."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product


def authorized(mask, matchings, m):
    for s, mate in enumerate(matchings):
        if (mask >> (2*m+s)) & 1:
            if all((mask & ((1 << i) | (1 << (m+j)))) for i, j in enumerate(mate)):
                return True
    return False


def replay(m, matchings, d, repeat=False):
    r = len(matchings)
    w = 1 if repeat else r
    pads = list(product(range(d), repeat=m*w))
    inverses = [tuple(mate.index(j) for j in range(m)) for mate in matchings]

    def share(secret, tape):
        vx = [tuple(tape[(0 if repeat else s)*m+i] for s in range(w))
              for i in range(m)]
        vy = [tuple(tape[(0 if repeat else s)*m+inverses[s][j]] for s in range(w))
              for j in range(m)]
        helpers = [(secret-sum(tape[(0 if repeat else s)*m:
                                    (0 if repeat else s)*m+m])) % d for s in range(r)]
        return tuple(vx+vy+helpers)

    rows = [[share(secret, pad) for pad in pads] for secret in range(d)]
    n = 2*m+r
    auth = unauth = 0
    for M in range(1 << n):
        C = tuple(j for j in range(n) if (M >> j) & 1)
        hist = [Counter(tuple(view[j] for j in C) for view in rs) for rs in rows]
        if authorized(M, matchings, m):
            seen = set()
            for x in range(d):
                assert not seen.intersection(hist[x])
                seen.update(hist[x])
            auth += 1
        else:
            assert all(h == hist[0] for h in hist)
            unauth += 1

    fibers = 0
    for k in range(2*m):
        side = range(0, m) if k < m else range(m, 2*m)
        rest = tuple(j for j in side if j != k)
        H = range(2*m, n)
        for x in range(d):
            by_rest = defaultdict(Counter)
            by_helper = defaultdict(Counter)
            for v in rows[x]:
                rest_value = tuple(v[j] for j in rest)
                by_rest[rest_value][v[k]] += 1
                by_helper[rest_value][tuple(v[j] for j in H)] += 1
            for b, dist in by_rest.items():
                assert len(dist) == d**w and len(set(dist.values())) == 1
                joint_helper = by_helper[b]
                assert len(joint_helper) == d**w and len(set(joint_helper.values())) == 1
                fibers += 1
    # Reweight the secret by nonuniform masses proportional to 1,2,...,d.
    # The complete distribution of a side and each helper remains identical.
    prior = [Fraction(x+1, d*(d+1)//2) for x in range(d)]
    for C in [tuple(range(m)), tuple(range(m, 2*m))] + [(2*m+s,) for s in range(r)]:
        weighted = defaultdict(Fraction)
        for x, rs in enumerate(rows):
            for v in rs:
                weighted[tuple(v[j] for j in C)] += prior[x]/len(pads)
        assert len(weighted) == (d**(m*w) if len(C) == m and C[0] < 2*m else d)
        assert set(weighted.values()) == {Fraction(1, len(weighted))}
    assert len(pads) == d**(m*w) and len(set(pads)) == len(pads)
    return auth, unauth, fibers, len(pads)*d


def cyclic(m, r):
    return [tuple((i+s) % m for i in range(m)) for s in range(r)]


cases = [(1,cyclic(1,1),2), (1,cyclic(1,1),3), (2,cyclic(2,1),4),
         (2,cyclic(2,2),2), (2,cyclic(2,2),3), (3,cyclic(3,2),2),
         (3,cyclic(3,3),2), (4,[(0,1,2,3),(1,0,3,2)],2)]
out = [replay(m, M, d) for m, M, d in cases]
auth, unauth, fibers, rows = map(sum, zip(*out))
a, b, f, _ = replay(2, [(0,1),(0,1)], 3, repeat=True)
assert a and b and f
print(f"probability PASS: {len(cases)} exact schemes, {rows} raw dealer rows, "
      f"{auth} authorized + {unauth} unauthorized views, {fibers} conditioned fibers")
print(f"probability PASS: nonuniform prior reweighting and repeated-matching negative control ({a+b} views)")
