"""Independent check: slope/intercept histograms, shoelace, integer weights."""

from itertools import combinations
from math import gcd, isqrt, prod
from random import Random


def graph_masses(n, weights):
    # Enumerate possible reduced slope values by a box in numerator/denominator,
    # not by forming secants between input points.
    natural = signed = rational = 0
    for den in range(1, n + 1):
        for num in range(-n, n + 1):
            if gcd(num, den) != 1:
                continue
            hist = {}
            for (x, y), w in weights.items():
                b = den * y - num * x
                hist[b] = hist.get(b, 0) + w
            rational = max(rational, max(hist.values()))
            if den == 1:
                signed = max(signed, max(hist.values()))
                if num >= 0:
                    natural = max(natural, max((w for b, w in hist.items() if b >= 0), default=0))
    return natural, signed, rational


def field_mass(weights, p):
    # Directly evaluate all affine parameters on residue histogram.
    residue = [[0]*p for _ in range(p)]
    for (x, y), w in weights.items():
        residue[x % p][y % p] += w
    used_x = [x for x, row in enumerate(residue) if any(row)]
    return max(sum(residue[x][(a*x+b) % p] for x in used_x)
               for a in range(p) for b in range(p))


def shoelace(A, B, C):
    x, y = A
    z, t = B
    u, v = C
    return x*t + z*v + u*y - y*z - t*u - v*x


def budget_sorted(M, ps):
    m = 1
    j = 0
    for p in sorted(ps):
        if m*p > M:
            break
        m *= p
        j += 1
    return j


def prime_from(k):
    for p in range(k, k + 10000):
        if p >= 2 and all(p % d for d in range(2, isqrt(p) + 1)):
            return p
    raise AssertionError("no prime found")


def full_check():
    rng = Random(57637)
    tests = full = short = pairs = tris = 0
    pooled_primes = ((2, 3), (5, 7), (3, 5, 11), (3, 7, 17, 31))
    for n in range(1, 13):
        P_large = prime_from(n*n+1)
        for test in range(16):
            points = rng.sample([(x, y) for x in range(n+1) for y in range(n+1)],
                                rng.randrange(1, min((n+1)**2, 11)+1))
            weights = {p: rng.randrange(1, 81) for p in points}
            total = sum(weights.values())
            nat, sig, rat = graph_masses(n, weights)
            ps = sorted(set(pooled_primes[test % len(pooled_primes)] + (P_large,)))
            total_bound = budget_sorted(n, ps) + budget_sorted(n*n, ps)
            evidence_sum = reverse = 0
            ds = [(shoelace(A, B, C), prod(weights[D] for D in (A, B, C)))
                  for A, B, C in combinations(points, 3)]
            assert all(abs(d) <= n*n for d, _ in ds)
            for p in ps:
                fld = field_mass(weights, p)
                delta = max(0, fld-rat)
                pair = 2 * total * sum(weights[A]*weights[B] for A, B in combinations(points, 2)
                                       if all((a-b) % p == 0 for a, b in zip(A, B)))
                trip = 6 * sum(w for d, w in ds if d and d % p == 0)
                # Counts here use a sum rather than the first checker's union.
                assert fld*delta**2 >= delta**3 and fld*delta**2 <= pair+trip
                evidence_sum += pair+trip
                reverse += fld < rat
                pairs += pair > 0
                tris += trip > 0
                assert nat <= sig <= fld
                if p > n*n:
                    assert rat == fld and (fld-sig)*(n//2+1) <= fld*(n//2)
                    full += 1
                if p > n:
                    assert (fld-nat)*(n+1) <= fld*n
                    short += 1
            assert evidence_sum <= total**3 * total_bound
            assert reverse <= budget_sorted(n, ps)
            tests += 1
    print(f"{tests} arbitrary weighted grids, {full} large-prime equalities, "
          f"{short} p>n checks, nonempty event counts pair={pairs}, determinant={tris}")


def all_ranges():
    for n in range(1, 13):
        p = prime_from(n+1)
        weights = {(x, n-x): 1 for x in range(n+1)}
        a, _, _ = graph_masses(n, weights)
        assert a == 1 and field_mass(weights, p) == n+1
        weights = {(x, x//2): 1 for x in range(0, n+1, 2)}
        _, a, _ = graph_masses(n, weights)
        assert a == 1 and field_mass(weights, prime_from(n*n+1)) == n//2+1
    print("Sharp deterministic constructions n=1..12: PASS")


if __name__ == "__main__":
    full_check()
    all_ranges()
