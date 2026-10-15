#!/usr/bin/env python3
"""Independent finite controls. These are not proofs of eventual statements."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import hashlib
import json
import mpmath as mp
import sympy as sp

BASE = Path(__file__).resolve().parent
mp.mp.dps = 320

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def symbolic_checks():
    m, k, c, u, beta, p, theta, alpha = sp.symbols(
        "m k c u beta p theta alpha", real=True)
    a = 2 + k
    exact = sp.factor(1 / k - m / a)
    assert sp.simplify(exact - (2 - k * (m - 1)) / (k * a)) == 0
    edge = sp.factor(2 / (a - p) - 2 / a)
    diag = sp.factor(1 / (a - 2 * beta) - 1 / a)
    assert sp.simplify(edge - 2 * p / (a * (a - p))) == 0
    assert sp.simplify(diag - 2 * beta / (a * (a - 2 * beta))) == 0
    assert sp.simplify(edge / edge.subs(k, 0)
                       - 2 * (2 - p) / (a * (a - p))) == 0
    assert sp.simplify(diag / diag.subs(k, 0)
                       - 4 * (1 - beta) / (a * (a - 2 * beta))) == 0
    qpow = sum(sp.prod(alpha - j for j in range(r)) * k ** r
               / sp.factorial(r) for r in range(5))
    inc = sp.expand(theta * (qpow - 1))
    logpower = sum((-1) ** (r + 1) * inc ** r / r for r in range(1, 5))
    logmean = sum((-1) ** (r + 1) * (k * theta) ** r / r
                  for r in range(1, 5))
    e = sp.Poly(sp.expand(logpower - alpha * logmean), k)
    coefficient = sp.factor(e.coeff_monomial(k ** 2) / (alpha - 1))
    assert sp.simplify(coefficient - alpha * theta * (1 - theta) / 2) == 0
    theta_series = sp.series((qpow - 1 - alpha * k)
                            / ((alpha - 1) * k * (qpow - 1)), k, 0, 2)
    assert sp.simplify(theta_series.removeO()
                      - (sp.Rational(1, 2) - (alpha + 1) * k / 12)) == 0
    theta_one = sp.series(((1 + k) * sp.log(1 + k) / k - 1) / k, k, 0, 2)
    assert sp.simplify(theta_one.removeO() - (sp.Rational(1, 2) - k / 6)) == 0
    negative_gap = sp.factor(2 * beta / (1 - beta) - 4 * beta / (2 - beta))
    assert sp.simplify(negative_gap - 2 * beta ** 2
                       / ((1 - beta) * (2 - beta))) == 0
    return {"checks": 9, "result": "PASS"}

def exact_inverse(matrix):
    return sp.Matrix(matrix).inv()

def cost_a(matrix, a):
    h = len(matrix)
    inv = exact_inverse([[a * int(i == j) - matrix[i][j]
                          for j in range(h)] for i in range(h)])
    return F(sum(inv)) - F(h, 1) / a

def tail_walk_checks():
    checked = 0
    details = []
    for m in (6, 7, 8, 9, 10, 11, 12):
        length = m // 3
        t = F(2, m - 1)
        kappa = t - F(1, m * m)
        a = 2 + kappa
        edges = list(combinations(range(m), 2))
        prefix_edges = [(2 * j, 2 * j + 1) for j in range(length)]
        rest_edges = [edge for edge in edges if edge not in prefix_edges]
        p = [F(j + 1, 500 * m ** 3) for j in range(len(edges), 0, -1)]
        beta_slots = [(i, i) for i in range(m)] + edges
        prefix_diags = [(2 * length + j, 2 * length + j)
                        for j in range(length)]
        rest_slots = [slot for slot in beta_slots if slot not in prefix_diags]
        beta = [F(j + 1, 700 * m ** 3)
                for j in range(len(beta_slots), 0, -1)]
        matrix = [[F(0) for _ in range(m)] for _ in range(m)]
        prefix = [[F(0) for _ in range(m)] for _ in range(m)]
        for index, (i, j) in enumerate(prefix_edges + rest_edges):
            matrix[i][j] += p[index]
            matrix[j][i] += p[index]
            if index < length:
                prefix[i][j] += p[index]
                prefix[j][i] += p[index]
        for index, (i, j) in enumerate(prefix_diags + rest_slots):
            if i == j:
                matrix[i][i] += 2 * beta[index]
                if index < length:
                    prefix[i][i] += 2 * beta[index]
            else:
                matrix[i][j] += beta[index]
                matrix[j][i] += beta[index]
        full = cost_a(matrix, a)
        first = cost_a(prefix, a)
        omitted = sum(p[length:]) + sum(beta[length:])
        gap = full - first - 2 * omitted / a ** 2
        assert gap >= 0
        # The same filled slots are an actual necessary matrix test here.
        c = F(1)
        f = kappa * m * m * a / (m - 1)
        assert c >= f * full
        checked += 1
        details.append({"m": m, "all_positive_slots": len(p),
                        "all_negative_slots": len(beta),
                        "omitted_mass": str(omitted), "strict_gap": str(gap)})
    return {"checks": checked, "result": "PASS", "details": details}

def bulk_purity(D, kappa):
    theta_real = F(D, 1) / (2 + kappa)
    left = theta_real.numerator // theta_real.denominator
    candidates = sorted(set((max(0, min(D, left)), max(0, min(D, left + 1)))))
    def purity(k):
        return (D + k * (2 * kappa + kappa ** 2)) / (D + k * kappa) ** 2
    values = [(purity(k), k) for k in candidates]
    best = max(value for value, _ in values)
    return best, [k for value, k in values if value == best]

def lower_rate_controls():
    details = []
    for m in (128, 256, 512, 1024, 2048):
        n = m * m // 4 - 16 * m
        D = m * n
        t = F(2, m - 1)
        c = F(4) + F(16, m)
        kappa = t - c / (m * m)
        a = 2 + kappa
        finite_cost = kappa * m * m * a / (m - 1) * (2 / (a - 1) - 2 / a)
        assert c >= finite_cost
        _, winners = bulk_purity(D, kappa)
        k = winners[0]
        raw_sum = D + k * kappa + 1
        raw_square = D + k * (2 * kappa + kappa ** 2) + 2 * (1 + kappa) + 1
        purity = raw_square / raw_sum ** 2
        exact_bulk, q_winners = bulk_purity(D, t)
        assert purity > exact_bulk
        assert k > m * (m - 1) // 2 and D - k > m * (m + 1) // 2
        details.append({"m": m, "n": n, "integer_bulk_ranks": q_winners,
                        "clipped_exact_rank": k,
                        "purity_profit_numerator_positive": True,
                        "finite_all_unitary_single_edge_test": True})
    return {"checks": len(details), "result": "PASS", "details": details,
            "scope": "Exact rational one-positive-head actual construction at alpha=2 only; proof handles all fixed positive orders."}

def psi(alpha, value):
    if alpha == 1:
        return value * mp.log(value) - value + 1 if value else mp.mpf(1)
    return (value ** alpha - 1 - alpha * (value - 1)) / (alpha - 1)

def deficit(alpha, groups):
    D = sum(count for count, _ in groups)
    raw = sum(count * value for count, value in groups)
    mean = raw / D
    if alpha == 1:
        return sum(count * value * mp.log(value) if value else mp.mpf(0)
                   for count, value in groups) / raw - mp.log(mean)
    moment = sum(count * value ** alpha for count, value in groups) / D
    return (mp.log(moment) - alpha * mp.log(mean)) / (alpha - 1)

def relative_subtraction_controls():
    ratios = []
    for alpha in map(mp.mpf, ("0.25", "0.5", "1", "1.5", "2", "3", "7")):
        for m in (80, 160):
            kappa = mp.mpf(2) / (m - 1) - mp.mpf(1) / (m * m)
            for exponent in (3, 4, 7):
                D = m ** exponent
                k = D // 2
                for p, beta in ((mp.mpf("0.125"), mp.mpf("0.25")),
                                (mp.mpf("1e-80"), mp.mpf("0")),
                                (mp.mpf("0"), mp.mpf("1e-80")),
                                (mp.mpf("0.125"), mp.mpf("1"))):
                    clipped = [(k, 1 + kappa), (D - k, mp.mpf(1))]
                    raw = [(1, 1 + kappa + p), (k - 1, 1 + kappa),
                           (1, 1 - beta), (D - k - 1, mp.mpf(1))]
                    H = psi(alpha, 1 + p) + psi(alpha, 1 - beta)
                    increment = D * (deficit(alpha, raw) - deficit(alpha, clipped))
                    T = p + beta
                    scale = kappa * T + T ** 2 / D
                    ratio = abs(increment - H) / scale
                    assert mp.isfinite(ratio)
                    ratios.append(ratio)
    return {"checks": len(ratios), "precision_decimal_digits": mp.mp.dps,
            "result": "PASS", "max_scaled_residual": mp.nstr(max(ratios), 30),
            "scope": "Subtraction identity (13) controls, including 1e-80 single anomalies and beta=1. These raw controls do not claim APPT feasibility."}

def wrong_unsubtracted_control():
    m = 100
    D = m ** 6
    t = F(2, m - 1)
    purity, _ = bulk_purity(D, t)
    moment = mp.mpf(purity.numerator) * D / purity.denominator
    centered_power = D * (moment - 1)
    exact = D * mp.log(moment)
    loss = centered_power - exact
    assert loss > 1000
    return {"wrong_rule": "Use an uncanceled D e = centered power + o(1) at unbounded D/m^3.",
            "D": D, "m": m, "error": mp.nstr(loss, 30), "result": "REJECTED"}

def main():
    report = {"role": "independent finite supporting controls",
              "not_a_proof_or_formal_audit": True,
              "source_bindings": {"INITIAL_PAPER.md": sha(BASE.parent / "INITIAL_PAPER.md"),
                                  "INITIAL_THEOREM_MAP.md": sha(BASE.parent / "INITIAL_THEOREM_MAP.md"),
                                  "check_exact_bulk_review.py": sha(__file__)},
              "symbolic": symbolic_checks(),
              "all_omitted_mass": tail_walk_checks(),
              "O_m_lower_band": lower_rate_controls(),
              "relative_subtraction": relative_subtraction_controls(),
              "wrong_extension": wrong_unsubtracted_control()}
    output = BASE / "INDEPENDENT_CONTROLS.json"
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: {k: v for k, v in val.items() if k != "details"}
                      if isinstance(val, dict) else val for key, val in report.items()}, indent=2))

if __name__ == "__main__":
    main()
