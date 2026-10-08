#!/usr/bin/env python3
"""Exact finite regressions for proof.tex; Python standard library only.

The analytic manuscript proves the arbitrary-body and nonatomic statements.
These checks do not substitute for those arguments. No assert statements are
used: running with Python -O retains every check.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial
from pathlib import Path
import json
import random


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def dot(x, y):
    return sum((a * b for a, b in zip(x, y)), F(0))


def norm2(x):
    return dot(x, x)


def det(rows):
    a = [list(map(F, row)) for row in rows]
    n, result = len(a), F(1)
    for k in range(n):
        pivot = next((j for j in range(k, n) if a[j][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        value = a[k][k]
        result *= value
        for j in range(k + 1, n):
            scale = a[j][k] / value
            for i in range(k + 1, n):
                a[j][i] -= scale * a[k][i]
    return result


def cols_det(cols):
    return det(list(zip(*cols)))


def base_anchors(d):
    return [tuple(F(-int(i == j), d) for j in range(d))
            for i in range(d)] + [(F(1, d),) * d]


def polar_vertices(d):
    # P=d(d+1)(conv(0,e_1,...,e_d)-(1,...,1)/(d+1)).
    return [tuple(F(d*d if i == j else -d) for j in range(d))
            for i in range(d)] + [(F(-d),) * d]


def weight_regressions(counts, rng):
    for d in range(2, 10):
        w, vertices = base_anchors(d), polar_vertices(d)
        lam = [F(1, d + 1)] * (d + 1)
        M = F(2*d*d)
        for i, v in enumerate(vertices):
            require(norm2(v) <= M*M, "polar radius")
            for j, x in enumerate(w):
                expected = F(-d if i == j else 1)
                require(dot(v, x) == expected, "polar vertex equations")
                require(lam[i] * (1 - dot(v, x)) == int(i == j),
                        "barycentric affine basis")
                counts["barycentric_basis_values"] += 1
        for _ in range(30):
            raw = [rng.randrange(1, 31) for _ in w]
            p = [F(x, sum(raw)) for x in raw]
            center = [sum((p[i]*w[i][j] for i in range(d+1)), F(0))
                      for j in range(d)]
            for i, v in enumerate(vertices):
                require(p[i] - lam[i] == -lam[i]*dot(v, center),
                        "exact weight correction")
                counts["weight_correction_values"] += 1
            total = sum(abs(p[i] - lam[i]) for i in range(d+1))
            require(total*total <= M*M*norm2(center),
                    "weight correction norm bound")
            counts["weight_bound_cases"] += 1


def constants_regressions(counts):
    records = []
    for d in range(2, 10):
        R0 = F(d*(d+1))
        b = 1 / (4*(d*R0)**d)
        M = 1/b
        Q = (d+1)*(d+2)*8**d*b**(-4*d)
        m, L = d-1, (d-1)*(M+1)
        J = F(d, 2)*(2*R0)**d*(1+M+d*2**(d-1)*M)
        rsharp = min(b, 1/(J*(8*M*d*L)**m))
        esharp = rsharp/(Q*(d+1))
        Asharp_power = (4*M*d*L)**m * J*Q*(d+1)
        require(Q*(d+1)*esharp <= b, "assignment gate")
        require(J*Q*(d+1)*esharp <= 1/(8*M*d*L)**m,
                "Hausdorff gate")
        require(Asharp_power*esharp <= F(1, 2)**m,
                "endpoint local threshold")
        C = 4*d*d*R0*(M+1)
        eold = 1/((d+1)*M*Q*(8*M*d*C)**d)
        Aold_power = (4*M*d*C)**d * M*Q*(d+1)
        require(Aold_power*eold == F(1, 2)**d,
                "preserved 1/d threshold")
        # The linear-assignment constant is checked from its unsimplified form.
        Nd, v0, q0, L0 = F((d+1)*(d+2), 2), b**d, b**(2*d)/4**d, 2**d/b**d
        require(2*L0*Nd/(q0*v0) == Q, "assignment constant algebra")
        require(F(2, d)**(d-1)/(d*(2*R0)**d) == 2*b,
                "dispersion constant algebra")
        counts["constant_dimensions"] += 1
        records.append({"d": d, "b": str(b), "Q": str(Q), "J": str(J),
                        "endpoint_threshold": str(esharp),
                        "old_threshold": str(eold),
                        "endpoint_A_to_power": str(Asharp_power)})
    return records


def polytope_regressions(counts):
    records = []
    for d in range(2, 10):
        anchors, vertices = base_anchors(d), polar_vertices(d)
        a, M, R0 = F(d*(d+1)), F(2*d*d), F(d*(d+1))
        lam = [F(1, d+1)] * (d+1)
        J = F(d, 2)*(2*R0)**d*(1+M+d*2**(d-1)*M)
        for t in (F(1, 100*d), F(1, 10*d), F(1, 4*d)):
            q, Z = t**(d-1), d*d-a*t
            cutpoint = (F(-1, Z),) * d
            points = anchors + [cutpoint]
            weights = [(1-q)/((d+1)*(1-t**d))]*d
            weights += [1/((d+1)*(1-t**d)),
                        (F(d, d+1)-t)*q/(1-t**d)]
            require(all(p > 0 for p in weights) and sum(weights) == 1,
                    "cone probabilities")
            require(all(norm2(x) <= 1 for x in points), "unit-ball cone support")
            mean = [sum((p*x[j] for p, x in zip(weights, points)), F(0))
                    for j in range(d)]
            require(mean == [0]*d, "truncation cone centering")
            p = weights[:-1]
            p[0] += weights[-1]
            err = tuple(cutpoint[j]-anchors[0][j] for j in range(d))
            h2 = weights[-1]**2 * norm2(err)
            center = tuple(sum((p[i]*anchors[i][j] for i in range(d+1)), F(0))
                           for j in range(d))
            require(norm2(center) <= h2, "assignment mean bound")
            correction = sum(abs(p[i]-lam[i]) for i in range(d+1))
            require(correction**2 <= M*M*h2, "cone weight bound")
            require(M*M*h2 <= 1, "small-error scale gate")
            for i, v in enumerate(vertices):
                require(p[i]-lam[i] == -lam[i]*dot(v, center),
                        "truncation barycentric correction")
            volP, volK = a**d/F(factorial(d)), a**d*(1-t**d)/F(factorial(d))
            z = t**d/(1-t**d)
            require(z*z <= M*M*h2, "transport mixed-volume bound")
            require(volP/volK <= (1+z)**d, "Minkowski scale bound")
            require((volP-volK)**2 <= (d*2**(d-1)*M*volK)**2*h2,
                    "absolute volume bound")
            c = a**(d-1)/F(factorial(d-1))
            normalsP = [tuple(-c*int(i == j) for j in range(d))
                        for i in range(d)] + [(c,)*d]
            normalsK = [tuple((1-q)*y for y in x) for x in normalsP[:-1]]
            normalsK += [(c,)*d, (-c*q,)*d]
            directions = [tuple(F(int(i == j)) for j in range(d))
                          for i in range(d)]
            directions += [(F(1),)*d,
                           tuple(F(1 if j == 0 else -1 if j == 1 else 0)
                                 for j in range(d)),
                           tuple(F(2 if j == 0 else -1) for j in range(d))]
            for u in directions:
                piP = sum(abs(dot(u, x)) for x in normalsP)/2
                piK = sum(abs(dot(u, x)) for x in normalsK)/2
                brightnessP = sum((l*abs(dot(u, x)) for l, x in zip(lam, anchors)), F(0))
                brightnessK = sum((p0*abs(dot(u, x)) for p0, x in zip(weights, points)), F(0))
                require(brightnessP == 2*piP/(d*volP), "simplex Cauchy identity")
                require(brightnessK == 2*piK/(d*volK), "truncation Cauchy identity")
                require((brightnessP-brightnessK)**2 <= (1+M)**2*norm2(u)*h2,
                        "normalized brightness transport")
                require(piP >= piK, "projection inclusion")
                require((piP-piK)**2 <= J*J*norm2(u)*h2,
                        "absolute projection bound")
                counts["projection_direction_cases"] += 1
            # u=(e1-e2)/sqrt(2) yields an exact projected truncation.
            projection_loss_squared = (c*q)**2/2
            gap_squared = a*a*t*t/d
            require(gap_squared**(d-1) <=
                    ((d-1)*(M+1))**(2*(d-1))*projection_loss_squared,
                    "projected cap exponent")
            require((z == t**d/(1-t**d)) and q == t**(d-1),
                    "two different cap orders")
            # Compute invariant directly from the centered cone law.
            A, B = F(0), F(0)
            for indices in combinations(range(d+2), d):
                wt = F(factorial(d))
                for i in indices:
                    wt *= weights[i]
                A += wt*abs(cols_det([points[i] for i in indices]))
            for indices in combinations(range(d+2), d+1):
                wt = F(factorial(d+1))
                for i in indices:
                    wt *= weights[i]
                B += wt*abs(cols_det([points[i]+(F(1),) for i in indices]))
            exact_e = q*(d*(d-1)-(d+1)*(d-2)*t-2*t**d) / (
                (d+1)*(1-t**d)*(d+1+(d-1)*q))
            require(A > 0 and B/((d+1)*A)-F(1, d+1) == exact_e,
                    "invariant from centered determinants")
            require(B-A == (d+1)*A*exact_e, "determinant deficit")
            counts["truncation_cone_cases"] += 1
            records.append({"d": d, "t": str(t), "error_squared": str(h2),
                            "defect": str(exact_e), "mixed_deficit": str(z),
                            "projection_loss_squared": str(projection_loss_squared)})
    return records


def witness_regressions(counts):
    records = []
    for d in (2, 3):
        anchors = base_anchors(d)
        for kind in ("simplex", "interior_zero", "symmetric_pair"):
            points = anchors[:]
            weights = [F(1, d+1)]*(d+1)
            if kind != "simplex":
                weights = [p/2 for p in weights]
                if kind == "interior_zero":
                    points += [(F(0),)*d]
                    weights += [F(1, 2)]
                else:
                    v = (F(1, 2*d),) + (F(0),)*(d-1)
                    points += [v, tuple(-x for x in v)]
                    weights += [F(1, 4)]*2
            N = len(points)
            require(all(sum(p*x[j] for p, x in zip(weights, points)) == 0
                        for j in range(d)), "finite law mean")
            require(all(norm2(x) <= 1 for x in points), "finite law support")
            covariance = [[sum(p*x[i]*x[j] for p, x in zip(weights, points))
                           for j in range(d)] for i in range(d)]
            lifted = [x+(F(1),) for x in points]
            table = {indices: cols_det([lifted[i] for i in indices])
                     for indices in product(range(N), repeat=d+1)}
            def prob(indices):
                answer = F(1)
                for i in indices:
                    answer *= weights[i]
                return answer
            A = sum((prob(indices)*abs(cols_det([points[i] for i in indices]))
                     for indices in product(range(N), repeat=d)), F(0))
            B = sum((prob(indices)*abs(value) for indices, value in table.items()), F(0))
            V2 = sum((prob(indices)*value*value for indices, value in table.items()), F(0))
            require(V2 == factorial(d+1)*det(covariance), "affine moment identity")
            D, cancellation, psi_mean = B-A, F(0), F(0)
            def psi(base, y, z):
                fy, fz = table[base+(y,)], table[base+(z,)]
                return min(max(fy, 0), max(-fz, 0)) + min(max(-fy, 0), max(fz, 0))
            for base in product(range(N), repeat=d):
                P = sum((weights[y]*max(table[base+(y,)], 0) for y in range(N)), F(0))
                Nm = sum((weights[y]*max(-table[base+(y,)], 0) for y in range(N)), F(0))
                cancellation += 2*prob(base)*min(P, Nm)
                for y, z in product(range(N), repeat=2):
                    psi_mean += prob(base)*weights[y]*weights[z]*psi(base, y, z)
                    counts["integrated_witness_sample_tuples"] += 1
            require(D == cancellation and D >= 0, "cancellation identity")
            require(psi_mean <= D, "two-sample witness expectation")
            R0 = F(d*(d+1))
            b = 1/(4*(d*R0)**d)
            Q = (d+1)*(d+2)*8**d*b**(-4*d)
            v0, q0, Nd = b**d, b**(2*d)/4**d, F((d+1)*(d+2), 2)
            event_mass, mean_H, selected = F(0), F(0), None
            for W, signed_V in table.items():
                H = F(0)
                for x in range(N):
                    total = F(0)
                    for i in range(d+1):
                        base = tuple(W[j] for j in range(d+1) if j != i)
                        total += psi(base, W[i], x)
                    for i, j in combinations(range(d+1), 2):
                        base = (x,) + tuple(W[k] for k in range(d+1) if k not in (i, j))
                        total += psi(base, W[i], W[j])
                    H += weights[x]*total
                mean_H += prob(W)*H
                if abs(signed_V) >= v0:
                    event_mass += prob(W)
                    if selected is None or H < selected[0]:
                        selected = (H, W, signed_V)
            require(mean_H <= Nd*D, "unconditioned anchor witnesses")
            require(event_mass >= q0, "conditioning probability")
            H, W, signed_V = selected
            require(H <= Nd*D/q0, "conditioned anchor choice")
            Phi, h1 = F(0), F(0)
            for x in range(N):
                alpha = []
                for i in range(d+1):
                    replacement = W[:i]+(x,)+W[i+1:]
                    alpha.append(table[replacement]/signed_V)
                require(sum(alpha) == 1, "barycentric sum")
                r = max(range(d+1), key=lambda i: (alpha[i], -i))
                require(alpha[r] > 0, "positive assigned coefficient")
                phi = sum(min(F(1), max(-a0, 0)) for a0 in alpha)
                phi += sum(min(max(alpha[i], 0), max(alpha[j], 0))
                           for i, j in combinations(range(d+1), 2))
                Phi += weights[x]*phi
                h1 += weights[x]*sum(abs(points[x][j]-points[W[r]][j])
                                    for j in range(d))
                # Identity of the first type of witness, not just its bound.
                for i in range(d+1):
                    base = tuple(W[j] for j in range(d+1) if j != i)
                    require(psi(base, W[i], x) ==
                            abs(signed_V)*min(F(1), max(-alpha[i], 0)),
                            "barycentric first witness")
                    counts["barycentric_witness_values"] += 1
                for i, j in combinations(range(d+1), 2):
                    base = (x,)+tuple(W[k] for k in range(d+1) if k not in (i, j))
                    require(psi(base, W[i], W[j]) >=
                            abs(signed_V)*min(max(alpha[i], 0), max(alpha[j], 0)),
                            "barycentric pair witness")
                    counts["barycentric_witness_values"] += 1
            require(abs(signed_V)*Phi <= H, "assignment witness integral")
            require(h1 <= 2*(2**d/v0)*Phi <= Q*D,
                    "linear assignment bound (L1 dominates Euclidean error)")
            counts["finite_centered_laws"] += 1
            records.append({"d": d, "law": kind, "A": str(A), "B": str(B),
                            "D": str(D), "witness_mean": str(psi_mean),
                            "selected_assignment_L1": str(h1),
                            "event_probability": str(event_mass)})
    return records


def matrix_regressions(counts, rng):
    for d in range(2, 8):
        n = d+1
        for _ in range(20):
            permutation = list(range(n))
            rng.shuffle(permutation)
            eta = F(1, 64*n)
            cols = []
            for j in range(n):
                raw = [rng.randrange(1, 51) for _ in range(n)]
                col = [eta*F(x, sum(raw)) for x in raw]
                col[permutation[j]] += 1-eta
                cols.append(col)
            determinant = abs(cols_det(cols))
            delta = 1-determinant
            require(0 <= delta <= F(1, 8), "near-maximum matrix gate")
            rows = []
            for col in cols:
                require(sum(x*x for x in col) >= (1-delta)**2,
                        "Hadamard column bound")
                i = max(range(n), key=lambda k: col[k])
                require(col[i] >= 1-2*delta, "dominant column entry")
                rows.append(i)
            require(len(set(rows)) == n, "distinct dominant rows")
            require(4*delta < 1-delta, "collision contradiction gate")
            counts["every_maximum_matrix_cases"] += 1


def main():
    counts = {key: 0 for key in (
        "constant_dimensions", "barycentric_basis_values",
        "weight_correction_values", "weight_bound_cases",
        "truncation_cone_cases", "projection_direction_cases",
        "finite_centered_laws", "integrated_witness_sample_tuples",
        "barycentric_witness_values", "every_maximum_matrix_cases")}
    rng = random.Random(20261007)
    weight_regressions(counts, rng)
    constants = constants_regressions(counts)
    polytopes = polytope_regressions(counts)
    witnesses = witness_regressions(counts)
    matrix_regressions(counts, rng)
    output = {"status": "all exact checks passed", "counts": counts,
              "constants": constants, "truncation_cone_records": polytopes,
              "witness_records": witnesses,
              "scope": "Finite rational regressions only. The general and nonatomic proof is in proof.tex."}
    Path(__file__).with_name("check_results.json").write_text(
        json.dumps(output, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": output["status"], "counts": counts}, sort_keys=True))


if __name__ == "__main__":
    main()
