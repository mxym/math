#!/usr/bin/env python3
"""Independent checks using a difference distribution, not cut incidences."""

from collections import Counter

if not __debug__:
    raise RuntimeError("Run without -O")


def dot(a, b):
    return (a & b).bit_count() & 1


def walsh_by_characters(f):
    N = len(f)
    return [
        sum((-1 if bo ^ dot(a, x) else 1) for x, bo in enumerate(f))
        for a in range(N)
    ]


def difference_distribution(points, N):
    dist = [0]*N
    for a in points:
        for b in points:
            dist[a ^ b] += 1
    return dist


def base(x, n):
    return sum((x >> j & 1) * (x >> (j+1) & 1) for j in range(0, n, 2)) % 2


def classify(f, r, sign, pos, label):
    N = len(f)
    m = N.bit_length()-1
    W = walsh_by_characters(f)
    A = 1 << ((m+r)//2)
    assert set(W) == {0, A, -A}
    assert W[0] == A*sign
    assert sum(x != 0 for x in W) == 1 << (m-r)
    D = [x for x, a in enumerate(f) if a]
    v = len(D)
    dist = difference_distribution(D, N)
    good = len({k for k in dist[1:] if k}) == 1
    assert good == pos, (r, sign, label)
    H = walsh_by_characters([int(not w) for w in W])
    # H function after rescaling: for nonzero t, Walsh(sign of
    # complement of S) = 2*H(t). Use autocorrelation independently.
    for t in range(1, N):
        assert (H[t]//2)*(1 << r) == N-4*v+4*dist[t]
    return v, dist


def graphs(n):
    M = 1 << n
    plain = [base(x, n) for x in range(M)]
    shear = [base(x ^ ((x >> 2) & 1), n) for x in range(M)]
    variants = [
        (plain + [a^1 for a in plain], 0, True, "bent graph"),
        (plain + [a^1 for a in shear], 0, False, "balanced non-affine support"),
        (plain + shear, 1, False, "unbalanced small support"),
        ([a^1 for a in plain + shear], -1, False, "unbalanced large support"),
    ]
    for f, sign, good, label in variants:
        classify(f, 1, sign, good, label)
    good_f = variants[0][0]
    D = [x for x, a in enumerate(good_f) if a]
    D.remove(D[0])
    assert len({d for d in difference_distribution(D, len(good_f))[1:] if d}) > 1
    print(f"m={n+1}: four plateaued concatenations and deleted-point control PASS")


def repeated(n):
    M = 1 << n
    Q = [base(x, n) for x in range(M)]
    classify(Q*4, 2, 1, n == 2, "positive, two periods")
    classify([b^1 for b in Q]*4, 2, -1, False, "negative, two periods")
    classify(Q + Q + [b^1 for b in Q]*2, 2, 0, False, "balanced with period")
    print(f"m={n+2}: three order-two plateaued lifts PASS")


if __name__ == "__main__":
    for n in (4, 6, 8):
        graphs(n)
    for n in (2, 4, 6):
        repeated(n)
