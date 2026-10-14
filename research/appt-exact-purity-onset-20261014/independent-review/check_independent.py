"""Independent finite controls for the complete written purity-onset proof.

Written without importing, calling, or rerunning the author's check script.
This checks finite algebra/witness examples; it is not a whole-domain proof.
Every execution writes its result, including exceptions, to a fresh log.
"""
from fractions import Fraction as F
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import traceback
import sympy as sp
import mpmath as mp

HERE = Path(__file__).resolve().parent
EVENTS = []


def exact(name, actual, expected=0):
    difference = sp.cancel(actual - expected)
    assert difference == 0, (name, difference)
    EVENTS.append({"kind": "symbolic", "name": name, "result": "exact"})


def ceil_fraction(value):
    return -((-value.numerator) // value.denominator)


def near_fraction(value):
    lower = value.numerator // value.denominator
    return lower + int(value - lower >= F(1, 2))


def solve_exact(matrix, rhs):
    work = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    for i in range(len(work)):
        pivot = next(j for j in range(i, len(work)) if work[j][i])
        work[i], work[pivot] = work[pivot], work[i]
        scale = work[i][i]
        work[i] = [value / scale for value in work[i]]
        for j in range(len(work)):
            if j != i:
                scale = work[j][i]
                work[j] = [v - scale * w for v, w in zip(work[j], work[i])]
    return [row[-1] for row in work]


def ldlt_psd(matrix, nullity=0):
    """Exact Schur elimination; tested matrices have no early zero pivot."""
    work = [list(row) for row in matrix]
    zeros = 0
    for i in range(len(work)):
        pivot = work[i][i]
        assert pivot >= 0, (i, pivot)
        if pivot == 0:
            assert all(work[i][j] == 0 for j in range(i, len(work)))
            zeros += 1
            continue
        for j in range(i + 1, len(work)):
            for k in range(j, len(work)):
                value = work[j][k] - work[j][i] * work[i][k] / pivot
                work[j][k] = work[k][j] = value
    assert zeros == nullity, (zeros, nullity)


def one_parameters(m, z):
    kap = F(2) / (m - 1 + z)
    a = 2 + kap
    p = a * z / (z + 2)
    c = m * m * (F(2, m - 1) - kap)
    return kap, a, p, c


def actual_single(m, n, z):
    d = m * n
    kap, a, p, c = one_parameters(m, z)
    bprime = d * (1 + kap) - kap * p - p * p
    optimum_trace = 2 * bprime / a
    optimum_rank = (optimum_trace - d - p) / kap
    rank = near_fraction(optimum_rank)
    trace = d + kap * rank + p
    square = d + (2 * kap + kap * kap) * rank + 2 * (1 + kap) * p + p * p
    purity = square / (trace * trace)
    relaxation = a * a / (4 * bprime)
    loss = a * a * (trace - optimum_trace) ** 2 / (4 * bprime * trace * trace)
    assert relaxation - purity == loss
    assert m * (m - 1) // 2 <= rank <= d - m * (m + 1) // 2
    return purity, relaxation, loss, rank, c


def qvalue(m, n, rank):
    t = F(2, m - 1)
    d = m * n
    return (d + (2 * t + t * t) * rank) / ((d + t * rank) ** 2)


def symbolic_checks():
    m, c, p, z, u, d, energy, mass, n = sp.symbols(
        "m c p z u D E T n", positive=True)
    t = 2 / (m - 1)
    kap = t - c / m ** 2
    a = 2 + kap
    bm = (m ** 2 - 1) / (4 * m ** 3)
    bp = d * (1 + kap) - kap * mass - energy
    v = energy + kap * mass - d / m ** 3 * (c - bm * c * c)
    exact("signed physical purity comparison",
          a * a / (4 * bp) - (2 + t) ** 2 / (4 * d * (1 + t)),
          (2 + t) ** 2 * v / (4 * d * (1 + t) * bp))
    ceff = 2 * kap * m * m * p / ((m - 1) * (2 + kap - p))
    exact("finite single-edge implicit derivative", sp.diff(c - ceff, c),
          1 + 2 * p * (2 - p) / ((m - 1) * (2 + kap - p) ** 2))
    kh = 2 / (m - 1 + z)
    ah = 2 + kh
    ph = ah * z / (z + 2)
    ch = m * m * (t - kh)
    ch_formula = 2 * m * m * z / ((m - 1) * (m - 1 + z))
    cost = ch - bm * ch * ch
    hh = 4 * m * (m + z) * (z * (m + z + 1) + 2) / ((2 * m + z) * (z + 2) ** 2)
    exact("finite exact cost coordinate", ch, ch_formula)
    exact("finite exact edge cost equality", ch,
          2 * kh * m * m * ph / ((m - 1) * (ah - ph)))
    exact("finite exact cost quadratic", cost, m * z * (2 * m + z) / (m - 1 + z) ** 2)
    exact("finite scalar crossing", ph * ph + kh * ph, cost * hh / (m * m))
    exact("boundary inverse sum", 2 / (ah - ph) + (m - 2) / ah, (m + z) / ah)
    exact("boundary rank-one product", kh * (m + z) / ah, 1)
    coeffs = [2 * z / (z + 2) ** 2,
              (3 * z * z + 2 * z + 4) / (z + 2) ** 2,
              (z ** 3 / 2 + z * z + 2 * z) / (z + 2) ** 2]
    series = sp.series((hh / m ** 2).subs(m, 1 / u), u, 0, 3).removeO().expand()
    for j, coefficient in enumerate(coeffs):
        exact("uniform scalar series coefficient " + str(j), series.coeff(u, j), coefficient)
    exact("critical curvature", sp.diff(coeffs[0], z, 2).subs(z, 2), -sp.Rational(1, 32))
    exact("critical displacement", -sp.diff(coeffs[1], z).subs(z, 2) /
          sp.diff(coeffs[0], z, 2).subs(z, 2), 8)
    exact("constant crossing correction", coeffs[2].subs(z, 2) +
          8 * sp.diff(coeffs[1], z).subs(z, 2) +
          32 * sp.diff(coeffs[0], z, 2).subs(z, 2), sp.Rational(7, 4))
    bb = (m * m + 5 * m + 7) / 4
    exact("rational lower displacement remainder", hh.subs(z, 2 + 8 / m) - bb,
          (21 * m ** 3 + 24 * m * m + 36 * m - 112) /
          (4 * (m + 2) ** 2 * (m * m + m + 4)))
    rank, trace = sp.symbols("k S", real=True)
    real_rank = d / (2 + t)
    pq = (d + (2 * t + t * t) * rank) / (d + t * rank) ** 2
    pb = (2 + t) ** 2 / (4 * d * (1 + t))
    exact("q integer rank loss", pb - pq,
          (2 + t) ** 2 * t * t * (rank - real_rank) ** 2 /
          (4 * d * (1 + t) * (d + t * rank) ** 2))
    odd_rank = ((m - 1) * n + 1) / 2
    H = n * (m * m - 1)
    exact("odd winning purity", pq.subs({d: m * n, rank: odd_rank}), m * (H + 2) / (H + 1) ** 2)
    exact("odd integer body rounding loss", pb.subs(d, m * n) - m * (H + 2) / (H + 1) ** 2,
          m / (H * (H + 1) ** 2))
    exact("actual trace rounding identity", a * a / (4 * bp) - (a * trace - bp) / trace ** 2,
          a * a * (trace - 2 * bp / a) ** 2 / (4 * bp * trace * trace))
    numerator = sp.cancel(sp.diff(hh, z) * (2 * m + z) ** 2 * (z + 2) ** 3 / (4 * m))
    return hh, numerator, m, z


def all_slot_mass_checks():
    for m in [8, 12, 16]:
        edges = [(i, j) for i in range(m) for j in range(i + 1, m)]
        positives = [(i, i) for i in range(m)] + edges
        R, K = len(edges), len(positives)
        pp = [F(1)] + [F(1, 1000 * R * i) for i in range(2, R)] + [F(0)]
        bb = [F(1, 2000 * K * i) for i in range(1, K)] + [F(0)]
        c = F(8)
        kap = F(2, m - 1) - c / (m * m)
        a = 2 + kap
        tau = sum(pp[1:], F(0)) + sum(bb, F(0))
        f = kap * m * m * a / (m - 1)
        for shift in [0, 1, K // 2]:
            P = [[F(0) for _ in range(m)] for _ in range(m)]
            for value, (i, j) in zip(pp, edges):
                P[i][j] += value
                P[j][i] += value
            assigned = positives[shift:] + positives[:shift]
            for value, (i, j) in zip(bb, assigned):
                if i == j:
                    P[i][i] += 2 * value
                else:
                    P[i][j] += value
                    P[j][i] += value
            A = [[(a if i == j else F(0)) - P[i][j] for j in range(m)] for i in range(m)]
            M = [[A[i][j] - kap for j in range(m)] for i in range(m)]
            ldlt_psd(M)
            resolvent = sum(solve_exact(A, [F(1)] * m), F(0))
            full_K = resolvent - F(m) / a
            primary_K = 2 / (a - pp[0]) - 2 / a
            rest_first = 2 * tau / (a * a)
            assert full_K >= primary_K + rest_first
            assert full_K > primary_K
            assert c >= f * full_K
            assert c >= f * primary_K + f * rest_first
            assert sum(sum(row, F(0)) for row in P) == 2 * (pp[0] + tau)
            EVENTS.append({"kind": "full_slots", "m": m, "R": R, "K": K,
                           "beta_slot_shift": shift, "full_slot_count": R + K,
                           "tail_mass": str(tau), "retained_first_walk_slack": str(full_K - primary_K - rest_first),
                           "physical_witness_PSD": True,
                           "scope": "finite protection matrices, not exhaustive all-pattern physical state"})


def boundary_checks():
    for m in [5, 7, 10]:
        z = F(2) + F(8, m)
        kap, a, p, c = one_parameters(m, z)
        assert p < a
        for edge in [(i, j) for i in range(m) for j in range(i + 1, m)]:
            P = [[F(0) for _ in range(m)] for _ in range(m)]
            i, j = edge
            P[i][j] = P[j][i] = p
            A = [[(a if r == s else F(0)) - P[r][s] for s in range(m)] for r in range(m)]
            M = [[A[r][s] - kap for s in range(m)] for r in range(m)]
            ldlt_psd(A)
            ldlt_psd(M, nullity=1)
            invones = solve_exact(A, [F(1)] * m)
            assert kap * sum(invones, F(0)) == 1
            assert all(sum(M[r][s] * invones[s] for s in range(m)) == 0 for r in range(m))
            EVENTS.append({"kind": "boundary_PSD", "m": m, "edge": edge,
                           "rank": m - 1, "strict_PD_false": True,
                           "exact_all_edge_conjugacy_control": True})


def rank_and_lattice_checks():
    for m in range(3, 11):
        for n in range(m, m + 9):
            d = m * n
            rank = ((m - 1) * n + 1) // 2
            values = [qvalue(m, n, k) for k in range(d + 1)]
            optimum = max(values)
            assert [k for k, value in enumerate(values) if value == optimum] == [rank]
            H = n * (m * m - 1)
            closed = F(m, H) if (m - 1) * n % 2 == 0 else F(m * (H + 2), (H + 1) ** 2)
            assert optimum == closed
            EVENTS.append({"kind": "exhaustive_q_rank", "m": m, "n": n,
                           "ranks_checked": d + 1, "unique_winner": rank})
    for m in [64, 65, 66, 67, 127, 128, 129, 256, 512, 1024, 4096]:
        B = F(m * m + 5 * m + 7, 4)
        N = ceil_fraction(B)
        assert B - B.numerator // B.denominator in [F(1, 4), F(3, 4)]
        assert N - B >= F(1, 4) and B - (N - 1) >= F(1, 4)
        z = F(2) + F(8, m)
        for n in [N - 1, N]:
            purity, relaxation, loss, rank, c = actual_single(m, n, z)
            body = qvalue(m, n, ((m - 1) * n + 1) // 2)
            real_body = F(m, n * (m * m - 1))
            profit = purity - body
            assert (profit > 0) if n == N - 1 else (profit < 0)
            assert (purity > real_body) if n == N - 1 else (relaxation < real_body)
            EVENTS.append({"kind": "actual_integer_single", "m": m, "n": n,
                           "rank": rank, "c": str(c), "profit": str(profit),
                           "rounding_loss": str(loss), "scope": "actual all-unitary single-head family only"})
    pole, body = F(32, 676), F(3, 64)
    assert pole > body
    EVENTS.append({"kind": "rejected_false_extension", "claim": "formula holds for every m>=3",
                   "m": 3, "n": 8, "pole_profit": str(pole - body)})
    m = 64
    n = ceil_fraction(F(m * m + 5 * m, 4))
    purity, _, _, rank, _ = actual_single(m, n, F(2) + F(8, m))
    body = qvalue(m, n, ((m - 1) * n + 1) // 2)
    assert purity > body
    EVENTS.append({"kind": "rejected_false_extension", "claim": "drop constant 7/4 from onset",
                   "m": m, "n": n, "actual_integer_rank": rank, "profit": str(purity - body)})


def compact_scalar_checks(h, numerator, msymbol, zsymbol):
    mp.mp.dps = 180
    for m in [64, 128, 256, 1024, 10 ** 6]:
        polynomial = sp.Poly(numerator.subs(msymbol, m), zsymbol)
        count = polynomial.count_roots(1, 3)
        assert count == 1
        coeffs = [mp.mpf(str(v)) for v in polynomial.all_coeffs()]
        root = mp.findroot(lambda z: mp.polyval(coeffs, z), (mp.mpf(2), 2 + mp.mpf(16) / m))
        hm = lambda z: 4 * m * (m + z) * (z * (m + z + 1) + 2) / ((2 * m + z) * (z + 2) ** 2)
        B = mp.mpf(m * m + 5 * m + 7) / 4
        gap = hm(root) - B
        assert 1 < root < 3
        assert abs(gap) < mp.mpf("0.125")
        EVENTS.append({"kind": "compact_scalar_maximum", "m": m,
                       "Sturm_roots_in_[1,3]": int(count), "root": mp.nstr(root, 75),
                       "max_h_minus_B": mp.nstr(gap, 75), "digits": mp.mp.dps,
                       "scope": "finite compact-scalar control; localization proof supplies applicability"})


def main():
    hh, numerator, msymbol, zsymbol = symbolic_checks()
    all_slot_mass_checks()
    boundary_checks()
    rank_and_lattice_checks()
    compact_scalar_checks(hh, numerator, msymbol, zsymbol)


if __name__ == "__main__":
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    report = {"utc_started": stamp, "scope": "independent finite ordinary controls; no Lean or full-domain certificate",
              "versions": {"sympy": sp.__version__, "mpmath": mp.__version__},
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), "events": EVENTS}
    try:
        main()
        report["status"] = "PASS_INDEPENDENT_FINITE_CONTROLS"
    except BaseException as exc:
        report["status"] = "FAIL_RETAINED"
        report["exception"] = repr(exc)
        report["traceback"] = traceback.format_exc()
        raise
    finally:
        counts = {}
        for event in EVENTS:
            counts[event["kind"]] = counts.get(event["kind"], 0) + 1
        report["counts"] = counts
        report["utc_finished"] = datetime.now(timezone.utc).isoformat()
        destination = HERE / ("RUN_" + stamp + ".json")
        destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({"status": report["status"], "counts": counts, "report": str(destination)}))
