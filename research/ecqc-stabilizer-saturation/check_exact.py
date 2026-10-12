#!/usr/bin/env python3
"""Exact finite replay for the ECQC stabilizer classification.

Only Python's standard library is used. Cyclotomic coefficients are integers;
no numerical eigensolver, entropy approximation, or external algebra system is
trusted. These finite tests supplement, not replace, the all-prime proof.
Copyright (c) 2026 Yongxian Zhang. All rights reserved.
"""
from __future__ import annotations
import json
import sys
from collections import Counter
from math import isqrt
from pathlib import Path

if not __debug__:
    raise SystemExit("Refusing optimized Python: run without -O.")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def is_prime(p: int) -> bool:
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


class Cyclo:
    """Z[zeta_p] in the basis 1,zeta,...,zeta^(p-2), with a zero final slot."""
    def __init__(self, p: int):
        require(p > 2 and is_prime(p), "An odd prime is required.")
        self.p = p
        self.zero = (0,) * p
        self.one = (1,) + (0,) * (p - 1)
        self.roots = tuple(self.canon([int(j == k) for j in range(p)])
                           for k in range(p))

    def canon(self, a):
        t = a[-1]
        return tuple(x - t for x in a)

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def scale(self, a, n: int):
        return tuple(n * x for x in a)

    def shift(self, a, k: int):
        p = self.p
        k %= p
        return self.canon([a[(i-k) % p] for i in range(p)])

    def conj(self, a):
        p = self.p
        return self.canon([a[-i % p] for i in range(p)])

    def mul(self, a, b):
        p = self.p
        c = [0] * p
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        c[(i+j) % p] += x*y
        return self.canon(c)

    def integer(self, a):
        require(all(x == 0 for x in a[1:]), "Not a rational integer.")
        return a[0]


def determinant(K, p):
    a, b, c, d = K
    return (a*d-b*c) % p


def image(K, v, p):
    a, b, c, d = K
    x, y = v
    return ((a*x+b*y) % p, (c*x+d*y) % p)


def invariant(K, v, p):
    x, y = v
    u, w = image(K, v, p)
    return (x*w-y*u) % p == 0


def all_det_minus_one(p):
    for a in range(1, p):
        inv = pow(a, -1, p)
        for b in range(p):
            for c in range(p):
                yield a, b, c, ((b*c-1)*inv) % p
    for b in range(1, p):
        c = pow(b, -1, p)
        for d in range(p):
            yield 0, b, c, d


def finite_field_replay(p):
    lines = [(0, 1)] + [(1, t) for t in range(p)]
    hist = Counter()
    scalar = []
    count = 0
    for K in all_det_minus_one(p):
        require(determinant(K, p) == p-1, "Wrong determinant generator.")
        count += 1
        m = sum(invariant(K, v, p) for v in lines)
        hist[m] += 1
        a, b, c, d = K
        if b == c == 0 and a == d:
            require((a*a+1) % p == 0 and m == p+1,
                    "Scalar extremizer mismatch.")
            scalar.append(a)
        else:
            require(m <= 2, "A nonscalar matrix has more than two eigenlines.")
    require(count == p*(p*p-1), "Wrong size of determinant fibre.")
    require(len(scalar) == (2 if p % 4 == 1 else 0), "Wrong square-root count.")
    return {"prime": p, "matrices": count, "invariant_line_histogram": dict(sorted(hist.items())),
            "scalar_roots_minus_one": scalar, "violating_stabilizer_rays": p*p*len(scalar)}


def density_numerator(p, K, alpha=1, beta=2, nonlinear=False):
    """Construct R=p^2 rho from actual Weyl matrices, without a state oracle."""
    require(determinant(K, p) == p-1, "K must have determinant -1.")
    F = Cyclo(p)
    D = p*p
    R = [[F.zero for _ in range(D)] for _ in range(D)]
    half = pow(2, -1, p)
    for a in range(p):
        for b in range(p):
            c, d = image(K, (a, b), p)
            chi = alpha*a+beta*b + (a*b if nonlinear else 0)
            common = half*(a*b+c*d)-chi
            for x in range(p):
                for y in range(p):
                    row = ((x+a) % p)*p+(y+c) % p
                    col = x*p+y
                    z = F.roots[(common+b*x+d*y) % p]
                    R[row][col] = F.add(R[row][col], z)
    return F, R


def check_density(F, R):
    p = F.p
    D = p*p
    require(len(R) == D and all(len(row) == D for row in R), "Wrong matrix shape.")
    trace = F.zero
    for i in range(D):
        trace = F.add(trace, R[i][i])
        for j in range(D):
            require(R[i][j] == F.conj(R[j][i]), "Density is not Hermitian.")
    require(trace == F.scale(F.one, D), "Density trace is not one.")
    for i in range(D):
        for j in range(D):
            v = F.zero
            for k in range(D):
                if R[i][k] != F.zero and R[k][j] != F.zero:
                    v = F.add(v, F.mul(R[i][k], R[k][j]))
            require(v == F.scale(R[i][j], D), "Density is not a rank-one projection.")
    for x in range(p):
        for z in range(p):
            A = B = F.zero
            for y in range(p):
                A = F.add(A, R[x*p+y][z*p+y])
                B = F.add(B, R[y*p+x][y*p+z])
            target = F.scale(F.one, p if x == z else 0)
            require(A == B == target, "A marginal is not I/p.")


def born_numerators(F, R, setting):
    """Direct Born rule, returning integers with common denominator p^4."""
    p = F.p
    if setting is None:
        return [[p*p*F.integer(R[j*p+k][j*p+k]) for k in range(p)]
                for j in range(p)]
    nonzero = [(i//p, i % p, h//p, h % p, v)
               for i, row in enumerate(R) for h, v in enumerate(row) if v != F.zero]
    table = []
    for j in range(p):
        row = []
        for k in range(p):
            total = F.zero
            for x, y, z, w, v in nonzero:
                phase = setting*(z*z+w*w-x*x-y*y)+j*(z-x)+k*(w-y)
                total = F.add(total, F.shift(v, phase))
            row.append(F.integer(total))
        table.append(row)
    return table


def check_table(p, table, perfect):
    require(len(table) == p and all(len(row) == p for row in table), "Wrong table shape.")
    require(all(v >= 0 for row in table for v in row), "Negative Born probability.")
    require(sum(map(sum, table)) == p**4, "Born probabilities do not sum to one.")
    require(all(sum(row) == p**3 for row in table), "Wrong Alice marginal.")
    require(all(sum(table[j][k] for j in range(p)) == p**3 for k in range(p)),
            "Wrong Bob marginal.")
    counts = Counter(v for row in table for v in row)
    expected = Counter({0: p*p-p, p**3: p}) if perfect else Counter({p*p: p*p})
    require(counts == expected, "Born table does not match the claimed exact law.")


def actual_density_replay(p, K, alpha=1, beta=2):
    F, R = density_numerator(p, K, alpha, beta)
    check_density(F, R)
    records = []
    for setting in [None]+list(range(p)):
        v = (0, 1) if setting is None else (1, 2*setting % p)
        perfect = invariant(K, v, p)
        table = born_numerators(F, R, setting)
        check_table(p, table, perfect)
        records.append({"setting": "infinity" if setting is None else setting,
                        "MI_over_log_p": int(perfect), "numerator_table": table,
                        "denominator": p**4})
    m = sum(rec["MI_over_log_p"] for rec in records)
    return {"prime": p, "K": list(K), "character_coefficients": [alpha, beta],
            "pure_density_and_both_partial_traces": "PASS", "Q_over_log_p": 2,
            "E_over_log_p": max(m-1, 0), "measurements": records}


def negative_controls():
    rejected = []
    def must_reject(name, fn):
        try:
            fn()
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError("Negative control was accepted: "+name)
    must_reject("determinant_plus_one", lambda: density_numerator(3, (1,0,0,1)))
    F, R = density_numerator(3, (1,0,0,2), nonlinear=True)
    must_reject("nonlinear_character", lambda: check_density(F, R))
    F, R = density_numerator(3, (1,0,0,2))
    R[0][1] = F.add(R[0][1], F.one)
    must_reject("corrupted_density", lambda: check_density(F, R))
    table = [[9]*3 for _ in range(3)]
    must_reject("independent_table_mislabeled_perfect", lambda: check_table(3, table, True))
    table[0][0] += 1
    must_reject("unnormalized_table", lambda: check_table(3, table, False))
    return rejected


def main():
    field = [finite_field_replay(p) for p in (3,5,7,11,13,17,19,29,31)]
    cases = [(3, (1,0,0,2)), (3, (0,1,1,1)),
             (5, (2,0,0,2)), (5, (1,0,0,4)),
             (5, (2,1,0,2)), (5, (0,1,1,2))]
    density = [actual_density_replay(p, K) for p, K in cases]
    result = {"status": "PASS", "arithmetic": "integer cyclotomic and finite-field arithmetic",
              "scope": "Finite exact replays; general quantifiers are proved in paper.tex.",
              "finite_field_replays": field, "actual_density_replays": density,
              "negative_controls_rejected": negative_controls()}
    out = Path(__file__).with_name("exact-replay.json")
    out.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "det_minus_one_matrices": sum(x['matrices'] for x in field),
                      "actual_density_cases": len(density), "negative_controls": 5,
                      "output": out.name}))

if __name__ == "__main__":
    main()
