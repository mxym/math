#!/usr/bin/env python3
"""Construct certificates, then check against literal restricted ANF."""
from collections import Counter
from functools import lru_cache
from random import Random


@lru_cache(None)
def windows(n, d):
    return tuple(sum(1 << ((j+i) % n) for i in range(d)) for j in range(n))


def constancy(x, free, n, d):
    frozen_zero = ((1 << n)-1) ^ (x | free)
    restricted = set()
    for term in windows(n, d):
        if term & frozen_zero:
            continue
        u = term & free
        if u in restricted:
            restricted.remove(u)
        else:
            restricted.add(u)
    return not (restricted - {0})


def keep_minimal(indices, length, d, cyclic):
    keep = list(indices)
    for z in indices if cyclic else indices[1:-1]:
        i = keep.index(z)
        if cyclic and len(keep) <= 2:
            break  # One zero cannot hit all windows since length > d.
        before, after = keep[i-1], keep[(i+1) % len(keep)]
        dist = (after-before) % length if cyclic else after-before
        if dist <= d:
            keep.pop(i)
    return set(keep)


def certificate(x, n, d):
    q, rho = divmod(n, d+2)
    h = d+2-rho
    need = min((rho+1)//2, h) if h <= q+1 else (rho+1)//2
    if not need:
        return 0, "zero deficit"
    bit = [(x >> i) & 1 for i in range(n)]
    if all(bit):
        return sum(1 << i for i in range(0, 2*need, 2)), "constant one"

    long_runs = []
    for i in range(n):
        if not bit[i] or bit[i-1]:
            continue
        L = 1
        while bit[(i+L) % n]:
            L += 1
        if L >= d:
            long_runs.append((i, L))
    if not long_runs:
        keep = keep_minimal([i for i in range(n) if not bit[i]], n, d, True)
        assert len(keep)*(d+1) <= 2*n
        return sum(1 << i for i in range(n) if i not in keep), "no long runs"

    free = 0
    b = len(long_runs)
    for j, (a, L) in enumerate(long_runs):
        M = (long_runs[(j+1) % b][0] - a - L) % n
        assert M > 0
        if b > q:
            if M == 1:
                free |= 1 << ((a+L) % n)
            continue

        def pref(i):
            return max(0, min(i+1, L-d+1)) % 2

        cand = [[], []]
        for i in range(L):
            if pref(i) == pref(i-d):
                cand[pref(i)].append((a+i) % n)
        assert len(cand[0])+len(cand[1]) >= L-d
        for i in max(cand, key=len):
            free |= 1 << i

        if M == 1:
            continue
        cluster = [(a+L+i) % n for i in range(M)]
        keep = keep_minimal([i for i in range(M) if not bit[cluster[i]]], M, d, False)
        assert 2*(M-len(keep)) >= M-2
        for i in range(M):
            if i not in keep:
                free |= 1 << cluster[i]
    return free, "many runs" if b > q else "few runs"


def main():
    coverage = Counter()

    def check(x, n, d):
        free, branch = certificate(x, n, d)
        q, rho = divmod(n, d+2)
        h = d+2-rho
        target = min((rho+1)//2, h) if h <= q+1 else (rho+1)//2
        assert free.bit_count() >= target, (x, n, d, branch)
        assert constancy(x, free, n, d), (x, n, d, branch)
        coverage[branch] += 1

    exhaustive = 0
    for d in (4, 6, 8):
        for n in range(2*d-1, 16):
            for x in range(1 << n):
                check(x, n, d)
                exhaustive += 1

    rng = Random(301711)
    larger = 0
    for d in range(4, 26, 2):
        for rho in range(d+2):
            for q in sorted({max(2, d//2-1), max(1, (2*d-1-rho+(d+1))//(d+2))}):
                n = q*(d+2)+rho
                assert n >= 2*d-1
                for sample in range(64):
                    if sample < 4:
                        x = (0, (1 << n)-1, (1 << (n-1))-1, ((1 << n)-1)//3)[sample]
                    else:
                        x = sum((rng.randrange(16) < sample % 16) << i for i in range(n))
                    check(x, n, d)
                    larger += 1

    # Two individually insensitive coordinates need not be jointly free.
    n, d, x, a, b = 14, 4, int("00111100111111", 2), 1, 4
    assert constancy(x, 1 << a, n, d)
    assert constancy(x, 1 << b, n, d)
    assert not constancy(x, (1 << a) | (1 << b), n, d)
    assert all(coverage[t] for t in ("zero deficit", "constant one", "no long runs", "few runs", "many runs"))
    print(f"exact: {exhaustive} exhaustive words, {larger} larger words; restricted ANF and negative control PASS")
    print("exact branches: " + ", ".join(f"{a}={b}" for a, b in sorted(coverage.items())))


if __name__ == "__main__":
    main()
