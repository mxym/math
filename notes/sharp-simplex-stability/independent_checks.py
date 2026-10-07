#!/usr/bin/env python3
"""Independent exact checks; no imports from the received package.

Rational affine simplexes with nonuniform zero weights, and rational
three-dimensional multiple-cut polytopes. Face cyclic ordering uses atan2;
all constructed vertices, areas, volumes, identities and inequalities are
then evaluated with exact Fraction arithmetic. This is finite evidence only.
"""
from fractions import Fraction as F
from itertools import combinations
from math import atan2
from pathlib import Path
import hashlib
import json
import random


def check(ok, text):
    if not ok:
        raise RuntimeError(text)


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def mul(k, a):
    return tuple(k*x for x in a)


def solve(A, b):
    n = len(A)
    z = [list(map(F, row))+[F(y)] for row, y in zip(A, b)]
    for i in range(n):
        piv = next((j for j in range(i, n) if z[j][i]), None)
        if piv is None:
            return None
        z[i], z[piv] = z[piv], z[i]
        v = z[i][i]
        z[i] = [a/v for a in z[i]]
        for j in range(n):
            if j != i:
                v = z[j][i]
                z[j] = [a-v*c for a, c in zip(z[j], z[i])]
    return tuple(row[-1] for row in z)


def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2],
            a[0]*b[1]-a[1]*b[0])


def anchor_checks(counts):
    rng = random.Random(71321007)
    records = []
    for d in range(2, 7):
        for case in range(24):
            # Triangular affine maps and translation produce skew, nonregular,
            # nonuniform zero-weight anchor simplexes wholly inside the ball.
            base = [tuple(F(-int(i == j), 4*d) for j in range(d))
                    for i in range(d)] + [(F(1, 4*d),)*d]
            A = [[F(rng.randrange(7, 15), 10) if i == j else
                  F(rng.randrange(-2, 3), 20) if i < j else F(0)
                  for j in range(d)] for i in range(d)]
            move = tuple(F(rng.randrange(-2, 3), 400*d*d) for _ in range(d))
            w = [add(tuple(dot(row, x) for row in A), move) for x in base]
            lam = solve([tuple(x[j] for x in w) for j in range(d)]+
                        [(F(1),)*(d+1)], (F(0),)*d+(F(1),))
            check(lam is not None and all(x > 0 for x in lam), "zero interior")
            q = [solve([w[j] for j in range(d+1) if j != i], (F(1),)*d)
                 for i in range(d+1)]
            check(all(x is not None for x in q), "polar vertices")
            M = max(sum(abs(y) for y in x) for x in q)
            check(all(dot(x, x) <= 1 for x in w), "anchors in unit ball")
            check(all(dot(x, x) <= M*M for x in q), "polar outer radius")
            for i in range(d+1):
                for j in range(d+1):
                    check(lam[i]*(1-dot(q[i], w[j])) == int(i == j),
                          "nonuniform barycentric affine basis")
                    counts["affine_basis_values"] += 1
            for _ in range(10):
                raw = [rng.randrange(1, 71) for _ in w]
                p = [F(x, sum(raw)) for x in raw]
                c = tuple(sum((p[i]*w[i][j] for i in range(d+1)), F(0))
                          for j in range(d))
                X = [sub(x, c) for x in w]
                check(all(dot(x, x) <= 1 for x in X), "original support in ball")
                check(all(sum(p[i]*X[i][j] for i in range(d+1)) == 0
                          for j in range(d)), "original law centered")
                for i in range(d+1):
                    check(p[i]-lam[i] == -lam[i]*dot(q[i], c),
                          "nonuniform exact correction")
                    counts["weight_correction_values"] += 1
                tv = sum(abs(p[i]-lam[i]) for i in range(d+1))
                check(tv*tv <= M*M*dot(c, c), "nonuniform correction bound")
                for _ in range(6):
                    u = tuple(F(rng.randrange(-5, 6), 3) for _ in range(d))
                    brightness_X = sum(p[i]*abs(dot(u, X[i])) for i in range(d+1))
                    brightness_T = sum(lam[i]*abs(dot(u, w[i])) for i in range(d+1))
                    check((brightness_X-brightness_T)**2 <=
                          (1+M)**2*dot(u, u)*dot(c, c),
                          "centered brightness comparison")
                    counts["nonuniform_brightness_cases"] += 1
                counts["weight_bound_cases"] += 1
            records.append({"dimension": d, "case": case,
                            "lambda": list(map(str, lam)), "M": str(M)})
    return records


def vertices(halfspaces):
    vv = set()
    for h in combinations(halfspaces, 3):
        v = solve([n for n, b in h], [b for n, b in h])
        if v is not None and all(dot(n, v) <= b for n, b in halfspaces):
            vv.add(v)
    return sorted(vv)


def facet_data(halfspaces, vv):
    ans = []
    for n, b in halfspaces:
        face = [v for v in vv if dot(n, v) == b]
        if len(face) < 3:
            continue
        center = tuple(sum(v[j] for v in face)/len(face) for j in range(3))
        axis = next(tuple(F(int(j == i)) for j in range(3))
                    for i in range(3) if any(cross(n, tuple(F(int(j == i))
                                                          for j in range(3)))))
        e = cross(n, axis)
        f = cross(n, e)
        face.sort(key=lambda v: atan2(float(dot(sub(v, center), f)),
                                     float(dot(sub(v, center), e))))
        area = (F(0),)*3
        for i, v in enumerate(face):
            area = add(area, mul(F(1, 2), cross(v, face[(i+1) % len(face)])))
        if dot(area, n) < 0:
            area = mul(-1, area)
        support_area = dot(area, face[0])
        check(support_area > 0 and dot(area, n) > 0, "outward face orientation")
        check(all(dot(area, x) == support_area for x in face), "facet support")
        ans.append((area, support_area))
    check(all(sum(a[j] for a, b in ans) == 0 for j in range(3)),
          "closed-polytope area-vector sum")
    volume = sum(b for a, b in ans)/3
    law = [(mul(1/b, a), b/(3*volume)) for a, b in ans]
    check(sum(p for x, p in law) == 1, "cone probabilities sum")
    check(all(sum(p*x[j] for x, p in law) == 0 for j in range(3)),
          "cone law centered")
    check(all(dot(x, x) <= 1 for x, p in law), "cone support in unit ball")
    return ans, volume, law


def closest_point(q, halfspaces):
    if all(dot(n, q) <= b for n, b in halfspaces):
        return q
    for k in range(1, 4):
        for hs in combinations(halfspaces, k):
            normals = [n for n, b in hs]
            gram = [[dot(n, m) for m in normals] for n in normals]
            mu = solve(gram, [dot(n, q)-b for n, b in hs])
            if mu is None or any(x < 0 for x in mu):
                continue
            correction = tuple(sum(mu[i]*normals[i][j] for i in range(k))
                               for j in range(3))
            x = sub(q, correction)
            if all(dot(n, x) <= b for n, b in halfspaces):
                check(all(dot(n, x) == b for n, b in hs), "KKT active equalities")
                return x
    raise RuntimeError("missing rational KKT projection")


def polytope_checks(counts):
    P_hs = [((F(-1), F(0), F(0)), F(2)),
            ((F(0), F(-1), F(0)), F(2)),
            ((F(0), F(0), F(-1)), F(2)),
            ((F(1), F(1), F(1)), F(2))]
    P_v = vertices(P_hs)
    P_faces, volumeP, Plaw = facet_data(P_hs, P_v)
    w = [x for x, p in Plaw]
    lam = [p for x, p in Plaw]
    q = [solve([w[j] for j in range(4) if j != i], (F(1),)*3)
         for i in range(4)]
    M = max(sum(abs(y) for y in x) for x in q)
    check(M == 10, "chosen outer radius")
    directions = [tuple(F(x) for x in xyz) for xyz in
                  [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1),
                   (1, -1, 0), (2, -3, 1), (-3, 1, 4), (2, 2, -3)]]
    cut_normals = [(-1, -1, -1), (1, 0, 0), (0, 1, 0), (0, 0, 1),
                   (2, -1, 0), (-1, 2, 0), (2, 1, -1)]
    records = []
    for tau in (F(1, 100), F(1, 10), F(1, 2), F(1), F(2)):
        for mode in range(7):
            ns = [tuple(F(x) for x in cut_normals[mode])]
            if mode >= 2:
                ns.append(tuple(F(x) for x in cut_normals[(mode+2) % 7]))
            if mode >= 5:
                ns.append(tuple(F(x) for x in cut_normals[(mode+4) % 7]))
            hs = P_hs[:]
            for n in ns:
                b = max(dot(n, v) for v in P_v)-tau
                check(b > 0 and b*b >= dot(n, n), "all cut bodies contain unit ball")
                hs.append((n, b))
            K_v = vertices(hs)
            K_faces, volumeK, Klaw = facet_data(hs, K_v)
            check(volumeK <= volumeP, "nested volumes")
            p = [F(0)]*4
            hupper = F(0)
            c = (F(0),)*3
            z = F(0)
            for X, weight in Klaw:
                # Genuine barycentric-max assignment in T, including cuts.
                alpha = [lam[i]*(1-dot(q[i], X)) for i in range(4)]
                check(sum(alpha) == 1, "affine coordinate partition")
                i = max(range(4), key=lambda k: (alpha[k], -k))
                p[i] += weight
                hupper += weight*sum(abs(y) for y in sub(X, w[i]))
                c = add(c, mul(weight, w[i]))
                z += weight*(max(dot(v, X) for v in P_v)-1)
            check(dot(c, c) <= hupper*hupper, "assigned mean bound")
            for i in range(4):
                check(p[i]-lam[i] == -lam[i]*dot(q[i], c), "cut-body exact correction")
            tv = sum(abs(p[i]-lam[i]) for i in range(4))
            check(tv*tv <= M*M*dot(c, c), "cut-body correction bound")
            check(0 <= z <= M*hupper, "first-variation transport bound")
            check(volumeP/volumeK <= (1+z)**3, "Minkowski scale bound")
            if M*hupper <= 1:
                check(volumeP-volumeK <= 12*M*hupper*volumeK,
                      "absolute volume deficit bound")
                counts["small_error_scale_cases"] += 1
            for u in directions:
                piP = sum(abs(dot(u, a)) for a, b in P_faces)/2
                piK = sum(abs(dot(u, a)) for a, b in K_faces)/2
                BP = sum(p0*abs(dot(u, x)) for x, p0 in Plaw)
                BK = sum(p0*abs(dot(u, x)) for x, p0 in Klaw)
                check(BP == 2*piP/(3*volumeP), "independent simplex Cauchy")
                check(BK == 2*piK/(3*volumeK), "independent multiple-cut Cauchy")
                check((BP-BK)**2 <= (1+M)**2*dot(u, u)*hupper*hupper,
                      "normalized projection comparison")
                check(piP >= piK, "projection inclusion monotonicity")
                Jbody = F(3, 2)*volumeK*(1+M+12*M)
                if M*hupper <= 1:
                    check((piP-piK)**2 <= Jbody*Jbody*dot(u, u)*hupper*hupper,
                          "absolute projection comparison")
                counts["polytope_projection_cases"] += 1
            # Hausdorff maxima are attained at vertices of the outer polytope,
            # since distance to a convex body is convex. Exact KKT projections.
            gaps = [(dot(sub(v, closest_point(v, hs)), sub(v, closest_point(v, hs))), v)
                    for v in P_v]
            s2, far = max(gaps)
            near = closest_point(far, hs)
            n = sub(far, near)
            check(s2 > 0 and dot(n, n) == s2, "positive Hausdorff gap")
            check(max(dot(n, v) for v in K_v) == dot(n, near), "separating support normal")
            u = next(cross(n, tuple(F(int(j == i)) for j in range(3)))
                     for i in range(3) if any(cross(n, tuple(F(int(j == i))
                                                          for j in range(3)))))
            check(dot(u, n) == 0 and dot(u, u) > 0, "gap-preserving projection direction")
            loss = (sum(abs(dot(u, a)) for a, b in P_faces)-
                    sum(abs(dot(u, a)) for a, b in K_faces))/2
            L = 2*(M+1)
            check(s2*s2*dot(u, u) <= L**4*loss*loss,
                  "independent projected-cap inequality")
            counts["polytope_cap_cases"] += 1
            records.append({"tau": str(tau), "mode": mode, "faces": len(K_faces),
                            "volume": str(volumeK), "z": str(z),
                            "assignment_L1_upper": str(hupper),
                            "Hausdorff_squared": str(s2),
                            "witness_projection_deficit_homogeneous": str(loss)})
    return records


def main():
    counts = dict.fromkeys(["affine_basis_values", "weight_correction_values",
                           "weight_bound_cases", "nonuniform_brightness_cases",
                           "polytope_projection_cases", "polytope_cap_cases",
                           "small_error_scale_cases"], 0)
    out = {"counts": counts, "anchors": anchor_checks(counts),
           "polytopes": polytope_checks(counts), "status": "PASS",
           "scope": "Finite independent rational regressions, not formal proof; cyclic face ordering uses atan2, and all subsequent identities and bounds use exact fractions."}
    path = Path(__file__).with_name("independent_certificate.json")
    path.write_text(json.dumps(out, indent=2)+"\n")
    print(json.dumps({"status": out["status"], "counts": counts,
                      "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest()},
                     sort_keys=True))


if __name__ == "__main__":
    main()
