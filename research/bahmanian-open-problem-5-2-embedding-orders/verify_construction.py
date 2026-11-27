#!/usr/bin/env python3
"""Verify the two-vacancy obstruction and the constructed filled blocks."""
from collections import Counter

if not __debug__:
    raise RuntimeError("Run without -O")


def cyclic(r, lam):
    return [[{(i+j+k) % r for k in range(lam)} for j in range(r)]
            for i in range(r)]


def counts(line):
    return Counter(s for cell in line for s in cell)


def row_and_col_deficits(A, lam):
    r = len(A)
    deficit = lambda line: Counter({s: lam for s in range(r)}) - counts(line)
    return list(map(deficit, A)), list(map(deficit, zip(*A)))


def bad_witness(r, lam, switch=True):
    A = cyclic(r, lam)
    a = (1-lam) % r
    b = (a-lam) % r
    A[0][a].remove(0)
    A[lam][b].remove(0)
    if switch:
        A[lam][a].remove(1)
        assert 0 not in A[lam][a]
        A[lam][a].add(0)
    return A


def check_bad_witness(r, lam):
    A = bad_witness(r, lam)
    a = (1-lam) % r
    b = (a-lam) % r
    flat = [len(cell) for row in A for cell in row]
    assert Counter(flat) == {lam-1: 2, lam: r*r-2}
    for line in [*A, *zip(*A)]:
        assert max(counts(line).values(), default=0) <= lam
    R, C = row_and_col_deficits(A, lam)
    assert R[0] == {0: 1} and C[a] == {1: 1}
    assert R[lam] == {1: 1} and C[b] == {0: 1}
    assert all(not deficit for j, deficit in enumerate(R) if j not in (0, lam))
    assert all(not deficit for j, deficit in enumerate(C) if j not in (a, b))
    assert all(lam*d*(r-d) > 2 for d in range(1, r))


def check_full_block(r, lam, n):
    mu, delta = lam-r, n-r
    assert 0 <= mu <= delta and delta >= r
    A = [[set(range(r)) | {r + (mu*(i+j)+k) % delta for k in range(mu)}
          for j in range(r)] for i in range(r)]
    assert all(len(cell) == lam for row in A for cell in row)
    for line in [*A, *zip(*A)]:
        mult = counts(line)
        assert all(lam-delta <= mult[k] <= lam for k in range(n))
    totals = counts([cell for row in A for cell in row])
    assert all(lam*(r-delta) <= totals[k] <= lam*(r-delta)+delta*delta
               for k in range(n))


if __name__ == "__main__":
    cases = 0
    for r in range(2, 41):
        for lam in range(1, r):
            if lam*(r-1) > 2:
                check_bad_witness(r, lam)
                cases += 1
    print(f"{cases} switched cyclic partial arrays through r=40 PASS")

    successes = failures = 0
    for r in range(1, 11):
        for lam in range(r, 3*r+1):
            for n in range(lam+1, max(2*r, lam)+6):
                if n >= max(2*r, lam):
                    check_full_block(r, lam, n)
                    successes += 1
                else:
                    delta = n-r
                    old_bottom_count = lam*delta-r*(lam-r)
                    assert old_bottom_count > delta*delta
                    failures += 1
    print(f"{successes} filled-block cases and {failures} fixed-order gaps PASS")

    r, lam = 7, 3
    A = bad_witness(r, lam, switch=False)
    a = (1-lam) % r
    b = (a-lam) % r
    R, C = row_and_col_deficits(A, lam)
    assert R[0] == C[a] == R[lam] == C[b] == {0: 1}
    print("no-switch control: both vacant slots can then be filled at r PASS")
