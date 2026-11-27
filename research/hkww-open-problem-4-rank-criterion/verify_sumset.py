#!/usr/bin/env python3
"""Check the geometric criterion against the intrinsic RM weight law."""

from collections import Counter
from itertools import combinations

if not __debug__:
    raise RuntimeError("Run without -O")


def linear_evaluation_weight(a, X):
    return sum((a & x).bit_count() & 1 for x in X)


def rm_by_weights(weights, m, rank):
    """Find a dimension m+1 subspace with exactly the RM(1,m) weights.

    Any such subspace contains the unique full-weight codeword. Once
    this is a basis row, all nonzero characters of the remaining m
    coefficient rows have sum 0 by the balanced-weight law. Fourier
    inversion implies their m-bit column profiles occur once each.
    """
    N = 1 << m
    if N not in weights:
        return False
    allones = weights.index(N)
    forbidden = [a for a, w in enumerate(weights) if w not in (0, N//2, N)]
    # The rank=m+2 assumption identifies dimension-m+1 subcodes with
    # the hyperplanes of the coefficient space.
    return any(
        not ((allones & normal).bit_count() & 1)
        and all((a & normal).bit_count() & 1 for a in forbidden)
        for normal in range(1, 1 << rank)
    )


def geometric_test(weights, X, m):
    pair_sums = {0}
    for x, y in combinations(X, 2):
        pair_sums.add(x ^ y)
    return (1 << m) in weights and len(pair_sums) < 1 << (m+1)


def exhaustive_m3():
    found = Counter()
    # Every code with all-one word can put it in the last generator
    # row. Then its eight columns are an arbitrary half of H=1.
    for X in combinations(range(16, 32), 8):
        W = [linear_evaluation_weight(a, X) for a in range(32)]
        if W.count(0) != 1:
            found["non-full rank"] += 1
            continue
        geom = geometric_test(W, X, 3)
        assert geom == rm_by_weights(W, 3, 5)
        found["RM present" if geom else "all-one but no RM"] += 1
    return found


def distinguished_examples():
    # 1 plus truth-table labels for F(t)=t0*t1 is a full-rank graph.
    X = [16 + 2*t + ((t & 3) == 3) for t in range(8)]
    W = [linear_evaluation_weight(a, X) for a in range(32)]
    assert W.count(0) == 1
    assert geometric_test(W, X, 3) and rm_by_weights(W, 3, 5)

    # No full-word line on these eight nonzero full-span columns:
    # {1,2,3} alone prevents a functional taking value one on all.
    X = [1, 2, 3, 4, 8, 16, 19, 25]
    W = [linear_evaluation_weight(a, X) for a in range(32)]
    assert W.count(0) == 1 and 8 not in W
    assert not geometric_test(W, X, 3) and not rm_by_weights(W, 3, 5)


if __name__ == "__main__":
    data = exhaustive_m3()
    assert data == {
        "non-full rank": 30, "RM present": 2760, "all-one but no RM": 10080
    }
    print(f"all 12870 half-hyperplanes at m=3: {dict(data)} PASS")
    distinguished_examples()
    print("full-rank graph and no-all-one control PASS")
