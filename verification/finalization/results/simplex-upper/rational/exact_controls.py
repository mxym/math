#!/usr/bin/env python3
"""Independent rational guards for the remaining sharp upper Main bridge.

These finite checks corroborate the written proof. They are not a Lean audit.
No package source, cache, or remote is modified.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def det(a):
    n = len(a)
    if n == 0:
        return F(1)
    return sum(((-1) ** j) * a[0][j] * det([r[:j] + r[j + 1:] for r in a[1:]])
               for j in range(n))


def inverse(a):
    n = len(a)
    rows = [[F(v) for v in row] + [F(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        i = next(i for i in range(j, n) if rows[i][j])
        rows[j], rows[i] = rows[i], rows[j]
        c = rows[j][j]
        rows[j] = [v / c for v in rows[j]]
        for i in range(n):
            if i != j:
                c = rows[i][j]
                rows[i] = [x - c * y for x, y in zip(rows[i], rows[j])]
    return [row[n:] for row in rows]


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def ensure(condition, message):
    if not condition:
        raise RuntimeError(message)


def polar_control(d):
    w = [[-F(1, d)] * d] + [[F(i == j) for j in range(d)] for i in range(d)]
    aug = [[F(1)] * (d + 1)] + [[w[i][j] for i in range(d + 1)] for j in range(d)]
    inv = inverse(aug)
    lam = [r[0] for r in inv]
    ell = [r[1:] for r in inv]
    b = F(1, 4 * d)
    M = 1 / b
    q = [[-x / lam[i] for x in ell[i]] for i in range(d + 1)]
    ensure(all(dot(x, x) <= 1 for x in w), "Unit-ball atoms")
    ensure(sum(lam) == 1 and all(x > 0 for x in lam), "Positive centered probabilities")
    ensure(all(sum(lam[i] * w[i][j] for i in range(d + 1)) == 0 for j in range(d)), "Center")
    ensure(all(lam[i] ** 2 >= b ** 2 * dot(ell[i], ell[i]) for i in range(d + 1)), "b-ball in T")
    ensure(all(dot(x, x) <= M ** 2 for x in q), "Outer radius")
    ensure(all(x >= b / (1 + b) for x in lam), "Quantitative positive weight")
    for i, j in product(range(d + 1), repeat=2):
        ensure(dot(q[i], w[j]) == 1 - F(i == j) / lam[i], "Polar pairing")
        ensure(lam[i] * (1 - dot(w[i], q[j])) == F(i == j), "Dual barycentric identity")
    tests = 0
    for numer in product(range(3), repeat=d + 1):
        if not sum(numer):
            continue
        beta = [F(k, sum(numer)) for k in numer]
        y = [sum(beta[i] * q[i][j] for i in range(d + 1)) for j in range(d)]
        ensure(all(dot(w[i], y) <= 1 for i in range(d + 1)), "Actual halfspace inclusion")
        ensure(beta == [lam[i] * (1 - dot(w[i], y)) for i in range(d + 1)], "Reconstruction")
        tests += 1
    return {"d": d, "b": str(b), "M": str(M), "weights": list(map(str, lam)),
            "convex_combinations_checked": tests}


def tetrahedron_brightness_counterexample():
    signs = [x for x in product([-1, 1], repeat=3) if x[0] * x[1] * x[2] == 1]
    pverts = [tuple(-t for t in x) for x in signs]
    kverts = [tuple(s * F(i == j) for j in range(3)) for i in range(3) for s in [-1, 1]]
    vp = abs(det([[pverts[i + 1][j] - pverts[0][j] for i in range(3)] for j in range(3)])) / 6
    vk = F(8, 6)  # The eight literal coordinate tetrahedra partition the octahedron.
    ensure(vp == F(8, 3) and vk == F(4, 3), "Actual volumes")
    ensure(all(dot(n, x) <= 1 for n in signs for x in kverts), "K subset P")
    ensure(all(max(dot(n, x) for x in kverts) == 1 for n in signs), "All original facets touch K")
    ensure(any(sum(abs(t) for t in x) > 1 for x in pverts), "K is strictly smaller")
    atoms_k = list(product([-1, 1], repeat=3))
    # Half-facet-area generators: P has n_i; K has s/4. Brightness is their absolute dot sum.
    directions = [u for u in product(range(-2, 3), repeat=3) if any(u)]
    for u in directions:
        pi_p = sum(abs(dot(n, u)) for n in signs)
        pi_k = sum(abs(dot(n, u)) for n in atoms_k) / F(4)
        ensure(pi_p / vp == pi_k / vk, "Normalized brightness equality")
        ensure(pi_p == 2 * pi_k and pi_k > 0, "Nonzero absolute projection deficit")
    hP = lambda x: max(dot(x, v) for v in pverts)
    support_test = sum(hP(x) for x in atoms_k) / F(8)
    ensure(support_test == 2, "Non-even support test detects missing scale")
    A = sum(abs(det([list(r) for r in zip(*p)])) for p in product(atoms_k, repeat=3)) / F(8 ** 3)
    B = sum(abs(det([[1] * 4] + [list(r) for r in zip(*p)]))
            for p in product(atoms_k, repeat=4)) / F(8 ** 4)
    ensure(A == F(3, 2) and B == F(45, 16), "Actual cube-atom iid moments")
    return {"dimension": 3, "volume_P": str(vp), "volume_K": str(vk), "ratio": str(vp/vk),
            "directions_checked": len(directions), "support_test_I": str(support_test),
            "A": str(A), "B": str(B), "D": str(B-A),
            "actual_entryDefect_via_audited_identity": str(B/(4*A)-F(1,4)),
            "D_over_B": str((B-A)/B)}


def original_constant_control(d):
    R0 = d * (d + 1)
    b = F(1, 4 * (d * R0) ** d)
    M = 1/b
    c = (d + 1) * (d + 2)
    Q = c * 8 ** d * M ** (4*d)
    L = (d-1) * (M+1)
    J = F(d,2) * (2*R0) ** d * (1+M+d*2**(d-1)*M)
    gate = min(b, 1/(J*(8*M*d*L)**(d-1)))
    e = gate/(Q*(d+1))
    ensure(M >= 1 and c*M**(d-1) <= Q, "Original Q radial absorption")
    ensure(M*gate <= 1, "Small scale")
    ensure(J*gate*(8*M*d*L)**(d-1) <= 1, "Root-free exact threshold")
    for t in [F(0), (d+1)*e/2, (d+1)*e, F(1), F(10)]:
        h = Q*t
        radial = 1 + d*M**d*c*t/(1+t)
        ensure(radial <= 1+d*M*h <= (1+M*h)**d, "Radial-to-original scale")
    return {"d":d, "absorbed_factor_le_original_Q": True,
            "exact_threshold_and_zero_endpoint": True}


def main():
    result = {"status": "PASS", "scope": "Finite rational corroboration; not a proof-assistant or arbitrary-body proof",
              "polar_duality": [polar_control(d) for d in range(2,7)],
              "actual_brightness_counterexample": tetrahedron_brightness_counterexample(),
              "original_constants": [original_constant_control(d) for d in range(3,9)]}
    path = Path(__file__).with_name("exact-controls.json")
    path.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
