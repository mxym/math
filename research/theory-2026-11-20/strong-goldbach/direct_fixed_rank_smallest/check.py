#!/usr/bin/env python3
"""Exact algebra replay for Proof.md, equations (2)--(4).

A log weight is the integer vector of its individual prime logarithms.
No floating logarithms, primality assumptions beyond the fixed labels,
or assertions disabled by python -O are used. This is a finite control
for the identities/endpoints, not a numerical test of the asymptotic.
"""
from itertools import chain, combinations, product
from math import prod

def need(flag, message):
    if not flag:
        raise RuntimeError(str(message))

def cross(tab, tags, coefficient):
    for t in tags:
        tab[t] += coefficient

def prep(p):
    full = (1 << len(p)) - 1
    masks = list(range(full + 1))
    idx = [[i for i in range(len(p)) if m & (1 << i)] for m in masks]
    val = [prod(p[i] for i in lst) for lst in idx]
    mu = [(-1) ** len(lst) for lst in idx]
    mu2 = [(-2) ** len(lst) for lst in idx]
    return full, masks, idx, val, mu, mu2

def partitions(full, tags):
    # Exactly one box for every label, not a divisor with multiplicity.
    for where in product(range(3), repeat=len(tags[full])):
        v = [0, 0, 0]
        for i, j in zip(tags[full], where):
            v[j] |= 1 << i
        yield tuple(v)

def one(p, cuts):
    full, masks, tags, val, mu, mu2 = prep(p)
    tail = full ^ 1
    td = [m for m in masks if not m & 1]
    rt1 = list(partitions(full, tags))
    rt0 = list(partitions(tail, tags))
    rminus, rplus, cap = cuts
    left, right = [[0] * len(p) for _ in range(2)]
    for d in masks:
        if val[d] > rminus:
            cross(left, tags[full ^ d], mu[d])
    for c, a, s in rt1:
        if val[c] < cap and val[a] > rplus:
            cross(left, tags[s], mu2[c])
    for d in td:
        if val[d] > rminus:
            right[0] += mu[d]
        if val[d] <= rminus < p[0] * val[d]:
            cross(right, tags[tail ^ d], -mu[d])
    for c, a, s in rt0:
        if val[a] > rplus and val[c] < cap:
            right[0] += mu2[c]
        if val[a] <= rplus < p[0] * val[a] and val[c] < cap:
            cross(right, tags[s], mu2[c])
        if val[a] > rplus and val[c] < cap <= p[0] * val[c]:
            cross(right, tags[s], 2 * mu2[c])
    need(left == right, (p, cuts, left, right))
    need(sum(abs(mu2[c]) for c, a, s in rt0) == 4 ** (len(p)-1),
         ("allocation coefficient", p))
    root1 = any(val[d] <= rminus < p[0] * val[d] for d in td)
    root2 = any(val[d] <= rplus < p[0] * val[d] for d in td)
    cap_event = any(val[d] < cap <= p[0] * val[d] for d in td)
    if not (root1 or root2 or cap_event):
        need(not any(left[1:]), ("no fringe", p, cuts, left))
    return (not (root1 or root2 or cap_event), root1, root2, cap_event)

def main():
    primes = [3, 5, 7, 13, 17, 23]
    counts = [0] * 5
    for p in chain.from_iterable(combinations(primes, r) for r in range(1, 7)):
        full, masks, tags, val, mu, mu2 = prep(p)
        # Include literal equality at both cut types, and its two neighbours.
        # Cyclic strides vary the two root cuts independently.
        distinct = sorted(set(val + [v + 1 for v in val] + [max(1,v-1) for v in val]))
        n = len(distinct)
        for i, u in enumerate(distinct):
            for r, s in [(0, 0), (1, 2), (2, 3), (3, 5), (5, 7)]:
                witness = one(p, (u, distinct[(i*r+s) % n], distinct[(i*s+r) % n]))
                counts[0] += 1
                for k, yes in enumerate(witness, 1):
                    counts[k] += yes
        # Explicit nonempty boxes with neither fringe possible.
        need(one(p, (0, 0, val[-1]+1))[0], ("missing no-fringe fixture", p))
    need(all(c > 0 for c in counts), ("coverage",counts))
    print("PASS exact vector identities:", counts[0],
          "fringe-free:", counts[1], "first-root:", counts[2],
          "second-root:", counts[3], "cap:", counts[4])

if __name__ == "__main__":
    main()
