#!/usr/bin/env python3
"""Exact cube check in the Boolean monomial basis, over the rationals."""
from itertools import combinations
from math import gcd
from collections import Counter


def reduce_integer(row, pivots):
    row = list(row)
    for p, b in sorted(pivots.items()):
        if row[p]:
            a = row[p]
            row = [b[p]*v - a*w for v, w in zip(row, b)]
            g = gcd(*row)
            if g:
                row = [v//g for v in row]
    return row


def realization_possible(rows, support, exterior):
    pivots = {}
    for x in exterior:
        row = reduce_integer(rows[x], pivots)
        if any(row):
            p = next(j for j, v in enumerate(row) if v)
            pivots[p] = row
    # Some nullspace vector survives all of the rows on the support
    # simultaneously iff no individual one is forced to be zero.
    return all(any(reduce_integer(rows[x], pivots)) for x in support)


def choices(n, degrees):
    return [[[int((u & x) == u) for u in range(1 << n) if u.bit_count() <= d]
             for x in range(1 << n)] for d in degrees]


def punctured_signed_cube(missing, k, n):
    if k <= 1:
        return len(missing) == (1 << k)-1
    origin = missing[0]
    span = {0}
    for x in missing[1:]:
        delta = x ^ origin
        if delta not in span:
            span |= {y ^ delta for y in span}
    if len(span) != 1 << k:
        return False
    # Every nonzero coordinate functional on this affine cube must be
    # a copy/complement of one of k independent block variables.
    directions = [sum(((v >> j) & 1) << i for i, v in enumerate(sorted(span)))
                  for j in range(n)]
    return len(set(directions) - {0}) == k


def stirling(n, k):
    row = [1] + [0]*n
    for _ in range(n):
        row = [0] + [j*row[j]+row[j-1] for j in range(1,n+1)]
    return row[k]


total = 0
for n in (1,2,3):
    N = 1 << n
    matrices = choices(n, range(n+1))
    degree = {}
    size_max = [0]*(N+1)
    endpoint = Counter()
    for S in range(1, 1 << N):
        inside = [x for x in range(N) if (S >> x) & 1]
        outside = [x for x in range(N) if not ((S >> x) & 1)]
        k = next(k for k, rows in enumerate(matrices)
                 if realization_possible(rows, inside, outside))
        degree[S] = k
        size_max[len(inside)] = max(size_max[len(inside)], k)
        if len(outside)+1 == 1 << k:
            assert punctured_signed_cube(outside,k,n)
            endpoint[k] += 1
    assert size_max[1:] == [(N-s+1).bit_length()-1 for s in range(1,N+1)]
    for k in range(n+1):
        assert endpoint[k] == (1 if k == 0 else N*stirling(n+1,k+1) if k >= 2 else N)
    rat_max = [0]*(N+1)
    for S in range(1,(1<<N)-1):
        s = S.bit_count()
        rat_max[s] = max(rat_max[s], degree[S],degree[((1<<N)-1)^S])
    for s in range(1,N):
        assert rat_max[s] == max((N-s+1).bit_length()-1,(s+1).bit_length()-1)
    total += len(degree)
    print(f"cube n={n}: all {len(degree)} nonempty supports; maxima={size_max[1:]}; endpoint counts={[endpoint[k] for k in range(n+1)]}")
print(f"cube cardinality and rational degree envelopes: {total} supports")

n = 4
N = 1 << n
matrices = choices(n,range(n+1))
for k in range(n+1):
    count = tested = 0
    for outside in combinations(range(N),(1<<k)-1):
        inside = [a for a in range(N) if a not in outside]
        found = k == 0 or not realization_possible(matrices[k-1],inside,outside)
        assert found == punctured_signed_cube(outside,k,n)
        if found:
            assert realization_possible(matrices[k],inside,outside)
        count += found
        tested += 1
    assert count == (1 if k == 0 else N if k == 1 else N*stirling(n+1,k+1))
    print(f"cube n=4 k={k}: {count} extremizers / {tested} critical-size supports")

# A size-3 support on the two-dimensional cube has, over F_2, the
# unique nonzero-label vector of weight 3, hence top coefficient 1.
indicator = [1,1,1,0]
assert sum(indicator) % 2 == 1
assert realization_possible(choices(2,[1])[0],[0,1,2],[3])
print("negative control: same size-3 support has degree 2 over F2 and 1 over Q: PASS")
