"""Exact k=7 obstruction for a Hoffman coclique of an SRG(99,14,1,2).

Python >=3.10, NumPy. All transforms, counts, masks and comparisons are integral.
No graph catalogue, isomorphism package, solver or search budget is used.
"""
from collections import Counter
from itertools import combinations
import numpy as np


def characters(n):
    return np.array([[(-1)**((u & v).bit_count()) for v in range(2**n)]
                     for u in range(2**n)], dtype=np.int16)


H4, H5, H6 = map(characters, (4, 5, 6))
CASES = [
    ((4, 4, 4), [0, 16, 1, 2, 4, 8, 13, 14], (73328, 96, 24, 0)),
    ((4, 4, 6), [0, 17, 18, 20, 24, 16, 28, 31], (93360, 84, 72, 0)),
    ((4, 4, 8), [0, 16, 1, 2, 4, 8, 7, 24], (57960, 552, 0, 24)),
    ((4, 6, 6), [0, 16, 1, 2, 4, 8, 15, 31], (58872, 0, 48, 0)),
]
PAIR = list(combinations(range(22), 2))
PI, PJ = np.array(PAIR).T


def xor(c):
    a = 0
    for b in c:
        a ^= b
    return a


def classify(S):
    # No selected block of four is inside a weight-eight word.
    values = H6[S]
    spectrum = values.sum(axis=0)
    assert set(map(abs, spectrum[1:])) == {2, 6}
    cuts = [sum(1 << j for j in range(22) if values[j, t] * spectrum[t] < 0)
            for t in range(1, 64) if abs(spectrum[t]) == 6]
    assert len(cuts) == 21 and all(c.bit_count() == 8 for c in cuts)
    pos = {p: i for i, p in enumerate(S)}
    options = {p: [] for p in PAIR}
    for i, j, k in combinations(range(22), 3):
        l = pos.get(S[i] ^ S[j] ^ S[k], -1)
        if l <= k:
            continue
        flat = (1 << i) | (1 << j) | (1 << k) | (1 << l)
        if any(flat & cut == flat for cut in cuts):
            continue
        for p in combinations((i, j, k, l), 2):
            options[p].append(flat)
    if min(map(len, options.values())) < 2:
        return 0
    must = {flat for opt in options.values() if len(opt) == 2 for flat in opt}
    assert len(must) > 77
    return len(must)


def run(dep, A, expected):
    assert tuple(sorted(len(c) for j in (2, 4, 6, 8) for c in combinations(A, j)
                        if xor(c) == 0)) == dep
    W = H5[A].sum(axis=0)
    n = {4: 6, 6: 7}[abs(W[16])]
    R = np.array(list(combinations(range(16), 14-n)))
    probes = H4[R].sum(axis=1)
    totals = Counter()
    count = 0
    for L in combinations(range(16), n):
        mask = sum(1 << x for x in L)
        if any(sum(1 << (x ^ d) for x in L) < mask for d in range(1, 16)):
            continue
        Q = H4[list(L)].sum(axis=0)
        ids = np.arange(len(R))
        for j in range(1, 16):
            h = probes[ids, j]
            good = np.ones(len(ids), dtype=bool)
            for w, v in ((W[j], Q[j]+h), (W[j+16], Q[j]-h)):
                for t in (w+v, w-v):
                    good &= (abs(t) == 2) | (abs(t) == 6)
            ids = ids[good]
        count += len(ids)
        if not len(ids):
            continue
        left = np.broadcast_to(np.array(A + [32+x for x in L]), (len(ids), 8+n))
        S = np.concatenate((left, 48+R[ids]), axis=1)
        # An occupied difference direction has at least three unordered pairs.
        directions = S[:, PI] ^ S[:, PJ]
        rows = 64*np.arange(len(ids))[:, None] + directions
        sizes = np.bincount(rows.ravel(), minlength=64*len(ids)).reshape(-1, 64)
        ok = np.all((sizes == 0) | (sizes >= 3), axis=1)
        for s in S[ok]:
            totals[classify(s.tolist())] += 1
    assert (count, totals[0], totals[78], totals[84]) == expected
    assert set(totals) <= {0, 78, 84}
    print(dep, 'spectral', count, 'directions', sum(totals.values()),
          'deficient', totals[0], 'forced78', totals[78], 'forced84', totals[84])


if __name__ == '__main__':
    for case in CASES:
        run(*case)
