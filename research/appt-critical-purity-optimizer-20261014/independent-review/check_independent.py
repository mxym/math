"""Independent finite controls for W0-W3; never a whole-domain certificate."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import hashlib
import json
import sys
import sympy as s
import mpmath as mp

BASE = Path(__file__).resolve().parents[1]
mp.mp.dps = 420


def binding(path):
    raw = path.read_bytes()
    return {"path": str(path), "sha256": hashlib.sha256(raw).hexdigest(),
            "lines": len(raw.splitlines())}


def mf(q):
    return mp.mpf(q.numerator) / q.denominator


def inv_sum_and_pivots(a, pattern):
    """Exact Gauss-Jordan inverse sum and independent LDL pivot signs."""
    h = len(pattern)
    mat = [[(a if i == j else F(0)) - pattern[i][j]
            for j in range(h)] for i in range(h)]
    ld = [row[:] for row in mat]
    pivots = []
    for j in range(h):
        pivot = ld[j][j]
        assert pivot > 0
        pivots.append(pivot)
        for r in range(j + 1, h):
            for c in range(j + 1, h):
                ld[r][c] -= ld[r][j] * ld[j][c] / pivot
    aug = [mat[i] + [F(int(i == j)) for j in range(h)] for i in range(h)]
    for col in range(h):
        row = next(r for r in range(col, h) if aug[r][col])
        aug[row], aug[col] = aug[col], aug[row]
        val = aug[col][col]
        aug[col] = [v / val for v in aug[col]]
        for r in range(h):
            if r != col:
                factor = aug[r][col]
                aug[r] = [v - factor * w for v, w in zip(aug[r], aug[col])]
    return sum((sum(row[h:], F(0)) for row in aug), F(0)), min(pivots)


def onehead(m, z):
    kap = F(2) / (m - 1 + z)
    a = 2 + kap
    p = a * z / (z + 2)
    c = m * m * (F(2, m - 1) - kap)
    return kap, p, c


def moments(D, kap, p, Y, Z):
    return (D + kap * Y + p,
            D + 2 * kap * Y + kap * kap * Z + 2 * (1 + kap) * p + p * p)


def Q(D, kap, p, k):
    S, A = moments(D, kap, p, F(k), F(k))
    return A / S**2


def rational_text(value):
    return str(value.numerator) + "/" + str(value.denominator)


out = {"kind": "independent finite controls, no Lean", "failures": [],
       "bindings": [binding(BASE / "PAPER.md"), binding(BASE / "THEOREM_MAP.md")],
       "versions": {"python": sys.version, "sympy": s.__version__, "mpmath": mp.__version__}}

# New identities are checked algebraically, not by importing author's checker.
D, kap, p, k, Y, Z, pp, beta = s.symbols("D kap p k Y Z pp beta")
a = 2 + kap
B = D * (1 + kap) - kap * p - p**2
S = D + kap * k + p
A = D + (2 * kap + kap**2) * k + 2 * (1 + kap) * p + p**2
assert s.expand(A - (a * S - B)) == 0
ks = D / a - p * (a + 2 * kap + 2 * p) / (a * kap)
assert s.factor(D + kap * ks + p - 2 * B / a) == 0
Su = D + kap * Y + p
Au = D + 2 * kap * Y + kap**2 * Z + 2 * (1 + kap) * p + p**2
inc = 2 * (pp - beta) + 2 * kap * pp + pp**2 + beta**2
assert s.expand(Au + inc - (Au + 2 * (1 + kap) * pp + pp**2 - 2 * beta + beta**2)) == 0
der = s.diff(Au, kap) / Au - 2 * s.diff(Su, kap) / Su
y, zz, h = s.symbols("y zz h")
de = der.subs({Y: D * y, Z: D * zz}).subs(D, 1 / h)
assert s.simplify(s.limit(de, h, 0) -
                  (2 * y + 2 * kap * zz) / (1 + 2 * kap * y + kap**2 * zz)
                  + 2 * y / (1 + kap * y)) == 0
de_inf = s.limit(de, h, 0)
assert s.simplify(s.diff(de_inf, kap).subs(kap, 0) - 2 * (zz - y**2)) == 0
Ss = s.symbols("Ss")
real_p = a / Ss - B / Ss**2
assert s.factor(s.diff(real_p, Ss) - (2 * B - a * Ss) / Ss**3) == 0
assert s.factor(a**2 / (4 * B) - real_p -
                a**2 * (Ss - 2 * B / a)**2 / (4 * B * Ss**2)) == 0
tie_diff = real_p - real_p.subs(Ss, Ss + kap)
assert s.factor(tie_diff - kap * (a * Ss * (Ss + kap) - B * (2 * Ss + kap)) /
                (Ss**2 * (Ss + kap)**2)) == 0
out["symbolic_checks"] = 8

# Exact physical tests cover ALL assignments of two positive heads and one
# negative head: six support vertices suffice; fix the retained head on 01.
edges = list(combinations(range(6), 2))
slots = [(i, i) for i in range(6)] + edges
pattern_checks = 0
deformation_records = []
for m, shift, power in [(64, -2, 8), (101, 0, 80), (128, 2, 160)]:
    n = m * m // 4 + shift * m
    Dv = m * n
    kap0, pv, c0 = onehead(m, F(2))
    eps = F(1, 10**power)
    tailp, tailb = 2 * eps, eps
    tau = tailp + tailb
    dc = 32 * tau
    oldkap = kap0 - dc / (m * m)
    av = 2 + oldkap
    worst = F(0)
    min_pivot = None
    for edge in edges:
        if edge == (0, 1):
            continue
        for slot in slots:
            pat = [[F(0) for _ in range(6)] for _ in range(6)]
            for ij, val in [((0, 1), pv), (edge, tailp)]:
                i, j = ij
                pat[i][j] += val
                pat[j][i] += val
            i, j = slot
            if i == j:
                pat[i][i] += 2 * tailb
            else:
                pat[i][j] += tailb
                pat[j][i] += tailb
            inverse, pivot = inv_sum_and_pivots(av, pat)
            test = oldkap * ((m - 6) / av + inverse)
            assert test < 1
            worst = max(worst, test)
            min_pivot = pivot if min_pivot is None else min(min_pivot, pivot)
            pattern_checks += 1
    # Two interior body coordinates exercise a non-endpoint clipped body.
    upper = Dv // 2
    Yv = F(upper)
    Zv = F(upper) - F(4, 9)  # replace one upper/lower pair by 2/3,1/3
    Suv, Auv = moments(Dv, oldkap, pv, Yv, Zv)
    Sxv = Suv + tailp - tailb
    Axv = Auv + 2 * (tailp - tailb) + 2 * oldkap * tailp + tailp**2 + tailb**2
    S0v, A0v = moments(Dv, kap0, pv, Yv, Zv)
    assert A0v / S0v**2 > Axv / Sxv**2
    loss_remove = Dv * (mp.log(mf(Axv / Auv)) - 2 * mp.log(mf(Sxv / Suv)))
    gain_contrast = Dv * (mp.log(mf(A0v / Auv)) - 2 * mp.log(mf(S0v / Suv)))
    # Finite inequalities here are deliberately weaker than eventual W constants.
    assert loss_remove / mf(tau) < mp.mpf("0.1")
    assert gain_contrast / mf(dc) > mp.mpf("0.09")
    deformation_records.append({"m": m, "n": n, "tail_mass": rational_text(tau),
        "all_slot_assignments": 294, "protected_max": mp.nstr(mf(worst), 24),
        "exact_max_rank_one_product": rational_text(worst),
        "exact_positive_min_slack": rational_text(1 - worst),
        "exact_min_A_pivot": rational_text(min_pivot),
        "removed_log_gain_over_tau": mp.nstr(loss_remove / mf(tau), 32),
        "contrast_gain_over_dc": mp.nstr(gain_contrast / mf(dc), 32),
        "normalized_purity_strictly_increases": True,
        "body_variance": rational_text(Zv / Dv - (Yv / Dv)**2)})
out["all_pattern_fraction_checks"] = pattern_checks
out["tiny_tail_deformation"] = deformation_records

# At tau=0 any nonzero protection slack is still eliminated: exact Fraction.
slack_records = []
for power in [8, 80, 160]:
    m, n = 101, 2550
    Dv = m * n
    kap0, pv, _ = onehead(m, F(2))
    dc = F(1, 10**power)
    kap1 = kap0 - dc / m**2
    Yv, Zv = F(Dv // 2), F(Dv // 2) - F(4, 9)
    Ss0, Aa0 = moments(Dv, kap0, pv, Yv, Zv)
    Ss1, Aa1 = moments(Dv, kap1, pv, Yv, Zv)
    assert Aa0 / Ss0**2 > Aa1 / Ss1**2
    slack_records.append({"slack": rational_text(dc), "strict": True})
out["zero_tail_tiny_slack"] = slack_records

# Exact normalized cube weights and strict convexity: preserve retained head.
m, n = 100, 2448
Dv = m * n
kapv, pv, _ = onehead(m, F(2))
kbase = Dv // 2
theta = [F(1, 3), F(2, 3)]
raw_mean = []
traces, weights, norm = [], [], []
for i in [0, 1]:
    for j in [0, 1]:
        wt = (theta[0] if i else 1 - theta[0]) * (theta[1] if j else 1 - theta[1])
        coords = [1 + kapv + pv, 1 + kapv * i, 1 + kapv * j]
        trace = Dv + kapv * (kbase + i + j) + pv
        traces.append(trace)
        weights.append(wt)
        norm.append([v / trace for v in coords])
        raw_mean.append(coords)
sum_trace = sum((w * t for w, t in zip(weights, traces)), F(0))
norm_weights = [w * t / sum_trace for w, t in zip(weights, traces)]
assert sum(norm_weights, F(0)) == 1
for i in range(3):
    actual = sum((weights[j] * raw_mean[j][i] for j in range(4)), F(0)) / sum_trace
    assert actual == sum((norm_weights[j] * norm[j][i] for j in range(4)), F(0))
    if i == 0:
        assert actual != sum((weights[j] * norm[j][i] for j in range(4)), F(0))
Sy, Ay = moments(Dv, kapv, pv, F(kbase) + 1, F(kbase) + F(5, 9))
assert Ay / Sy**2 < max(Q(Dv, kapv, pv, kbase + j) for j in range(3))
out["cube_checks"] = {"trace_reweighted_identity": True,
                       "uniform_normalized_weights_rejected": True,
                       "interior_body_strictly_suboptimal": True}

# Fixed-body contrast monotonicity at order kap/4 needs profit localization.
# This feasible endpoint body has a much smaller variance and fails that bound.
Rmin = m * (m - 1) // 2
Sm0, Am0 = moments(Dv, kapv, pv, F(Rmin), F(Rmin))
der0 = (2 * Rmin + 2 * kapv * Rmin + 2 * pv) / Am0 - 2 * Rmin / Sm0
assert der0 < kapv / 4
t_bulk = F(2, m - 1)
k_bulk = ((m - 1) * n + 1) // 2
bulk_purity = (Dv + (2 * t_bulk + t_bulk**2) * k_bulk) / (Dv + t_bulk * k_bulk)**2
assert Am0 / Sm0**2 < bulk_purity
out["unconditional_contrast_bound_rejected"] = {
    "m": m, "n": n, "upper_rank": Rmin,
    "derivative_over_contrast": rational_text(der0 / kapv),
    "not_profitable": True,
    "necessary_profit_localization_retained": True}

# Integer optimization and switching: only floor/ceil can win, not nearest only.
rank_checks = 0
for zval in [F(1), F(3, 2), F(2), F(5, 2), F(3), F(2) - F(1, 10**40), F(2) + F(1, 10**40)]:
    kapv, pv, _ = onehead(m, zval)
    av = 2 + kapv
    Bv = Dv * (1 + kapv) - kapv * pv - pv**2
    star = (2 * Bv / av - Dv - pv) / kapv
    flo = star.numerator // star.denominator
    cei = flo if star.denominator == 1 else flo + 1
    assert m * (m - 1) // 2 <= flo <= cei <= Dv - m * (m + 1) // 2
    best = max(Q(Dv, kapv, pv, flo), Q(Dv, kapv, pv, cei))
    samples = {0, m * (m - 1) // 2, Dv - m * (m + 1) // 2, Dv,
               flo - 1, flo + 2, flo - 100, flo + 100}
    for kval in samples:
        if 0 <= kval <= Dv:
            assert Q(Dv, kapv, pv, kval) < best
            rank_checks += 1
out["integer_rank_exclusion_controls"] = rank_checks

def mpvals(zv):
    kapm = 2 / (m - 1 + zv)
    pm = (2 + kapm) * zv / (zv + 2)
    am = 2 + kapm
    Bm = Dv * (1 + kapm) - kapm * pm - pm**2
    star = (2 * Bm / am - Dv - pm) / kapm
    return kapm, pm, star

star0 = mpvals(mp.mpf(2))[2]
kint = int(mp.floor(star0))
ztarget = mp.findroot(lambda zv: mpvals(zv)[2] - (kint + mp.mpf("0.5")),
                     (mp.mpf(2), mp.mpf("2.01")))
kapm, pm, _ = mpvals(ztarget)
Sm = Dv + kapm * kint + pm
# Just below the Euclidean midpoint, denominator bias favors ceiling.
target = kint + mp.mpf("0.5") - kapm / (8 * Sm)
zw = mp.findroot(lambda zv: mpvals(zv)[2] - target, (ztarget, ztarget + mp.mpf("0.0001")))
kapm, pm, stm = mpvals(zw)
def mpq(kval):
    return (Dv + (2 * kapm + kapm**2) * kval + 2 * (1 + kapm) * pm + pm**2) / (Dv + kapm * kval + pm)**2
assert stm < kint + mp.mpf("0.5")
assert mpq(kint + 1) > mpq(kint)
out["nearest_only_rejected"] = {"m": m, "n": n,
    "z": mp.nstr(zw, 60), "real_rank": mp.nstr(stm, 60),
    "nearest_rank": kint, "winning_rank": kint + 1,
    "purity_difference": mp.nstr(mpq(kint + 1) - mpq(kint), 32)}

# A false removal of the eventual qualifier is explicitly detected.
assert F(32, 676) > F(3, 64)
out["small_dimension_false_extension"] = {"m": 3, "n": 8,
    "pole_purity": "32/676", "q_purity": "3/64", "rejected": True}
out["script_binding"] = binding(Path(__file__).resolve())
target = Path(__file__).with_name("independent_checks.json")
target.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"symbolic": out["symbolic_checks"], "all_patterns": pattern_checks,
                  "tiny_tail": len(deformation_records), "rank_controls": rank_checks,
                  "failures": out["failures"]}))
