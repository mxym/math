#!/usr/bin/env python3
from fractions import Fraction as F
from math import factorial, comb, sqrt


def require(cond, msg):
    if not cond:
        raise SystemExit("FAIL: " + msg)


def pstrip(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    out = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return pstrip(out)


def pmul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return pstrip(out)


def pder(p):
    return pstrip([F(i) * p[i] for i in range(1, len(p))] or [F(0)])


def peval(p, x):
    z = F(0)
    for c in reversed(p):
        z = z * x + c
    return z


def exp_partial(x, n):
    s = F(1)
    term = F(1)
    for k in range(1, n + 1):
        term *= x / F(k)
        s += term if k % 2 == 0 else -term
    return s


def exp_bounds(x):
    require(F(0) <= x < F(1), "alternating exponential domain")
    # For 0 <= x < 1 the alternating terms decrease:
    # odd truncation <= exp(-x) <= even truncation.
    return exp_partial(x, 13), exp_partial(x, 12)


# ---------------------------------------------------------------------------
# Exact five-term lower witness
# ---------------------------------------------------------------------------
# A(x)=sum c_k x^k; the Fock coefficients are a_k=c_k*sqrt(k!).
c = [
    F(1),
    F(750737, 500000),
    F(-232953, 500000),
    F(-25879, 1000000),
    F(-2229, 1000000),
    F(-163, 1000000),
]

even = [c[0], c[2], c[4]]
odd = [c[1], c[3], c[5]]
P = padd(pmul(even, even), [F(0)] + pmul(odd, odd))
qcrit = padd(pder(P), [-z for z in P])

require(qcrit[0] > 0, "critical polynomial starts positive")
require(
    all(z < 0 for z in qcrit[1:]),
    "critical polynomial is strictly decreasing on y >= 0",
)
require(all(z >= 0 for z in P), "P is nondecreasing on y >= 0")

L = F(2957298, 10000000)
U = F(2957299, 10000000)
require(
    peval(qcrit, L) > 0 and peval(qcrit, U) < 0,
    "unique critical root bracket",
)

S = sum(F(factorial(k)) * c[k] * c[k] for k in range(len(c)))
H = sum(
    F(k * factorial(k)) * c[k] * c[k]
    for k in range(1, len(c))
)

# Degree 10 is even, hence an upper truncation for exp(-L).
eL_upper = exp_partial(L, 10)
M_upper = 2 * eL_upper * peval(P, U)
N_lower = 2 * S - M_upper
target = F(6238973, 10000000)

require(N_lower > 0, "positive certified numerator")
require(
    N_lower * N_lower > 16 * target**4 * S * H,
    "0.6238973 lower constant",
)


# ---------------------------------------------------------------------------
# Exact dual ceiling for the full completed profile class
# ---------------------------------------------------------------------------
Q = F(779, 2000)  # Lambda_profile <= 0.3895.


def la_add(a, b):
    z = dict(a)
    for k, v in b.items():
        z[k] = z.get(k, F(0)) + v
    return {k: v for k, v in z.items() if v}


def la_mul(a, b):
    z = {}
    for i, x in a.items():
        for j, y in b.items():
            z[i + j] = z.get(i + j, F(0)) + x * y
    return {k: v for k, v in z.items() if v}


def la_scale(a, s):
    return {k: s * v for k, v in a.items() if s * v}


def times_t2(a):
    require(min(a) >= -2, "Laurent degree")
    hi = max(a)
    return pstrip([a.get(k - 2, F(0)) for k in range(hi + 3)])


def certificate_polynomials(y):
    e1_lo, _e1_hi = exp_bounds(y)
    e2_lo, e2_hi = exp_bounds(2 * y)

    # Exact tail identities are
    # T_even=(1+exp(-2y))/2-exp(-y)
    # T_odd =(1-exp(-2y))/2-y exp(-y).
    # The following are certified upper bounds.
    Te_hi = (1 + e2_hi) / 2 - e1_lo
    To_hi = (1 - e2_lo) / 2 - y * e1_lo
    require(Te_hi >= 0 and To_hi >= 0, "tail upper bounds")

    # d_k(t)=2 Q t k - 2 + 2 Q/t.
    d0 = {-1: 2 * Q, 0: F(-2)}
    d1 = la_add(d0, {1: 2 * Q})
    d2 = la_add(d0, {1: 4 * Q})
    d3 = la_add(d0, {1: 6 * Q})

    # Multiplying the sufficient Schur inequalities by their positive
    # denominators gives:
    # E=d0(d2+2Te_hi)+2 e1_lo d2,
    # O=d1(d3+2To_hi)+2 y e1_lo d3.
    E = la_add(
        la_mul(d0, la_add(d2, {0: 2 * Te_hi})),
        la_scale(d2, 2 * e1_lo),
    )
    O = la_add(
        la_mul(d1, la_add(d3, {0: 2 * To_hi})),
        la_scale(d3, 2 * y * e1_lo),
    )
    return times_t2(E), times_t2(O)


def substitute_unit_interval(p, a, b):
    # Return p(a+(b-a)u) in the power basis.
    n = len(p) - 1
    h = b - a
    q = [F(0)] * (n + 1)
    for i, ci in enumerate(p):
        for j in range(i + 1):
            q[j] += (
                ci
                * F(comb(i, j))
                * a ** (i - j)
                * h**j
            )
    return pstrip(q)


def bernstein_coeffs(p, a, b):
    # If q(u)=sum_j q_j u^j has degree n, then its degree-n
    # Bernstein coefficients are
    # beta_k=sum_{j<=k} q_j C(k,j)/C(n,j).
    q = substitute_unit_interval(p, a, b)
    n = len(p) - 1
    require(len(q) <= n + 1, "degree")
    q += [F(0)] * (n + 1 - len(q))
    out = []
    for k in range(n + 1):
        out.append(
            sum(
                q[j] * F(comb(k, j), comb(n, j))
                for j in range(k + 1)
            )
        )
    return out


segments = [
    ("0.47", "0.8", "0.304"),
    ("0.8", "1.015", "0.304"),
    ("1.015", "1.045", "0.300"),
    ("1.045", "1.055", "0.299"),
    ("1.055", "1.065", "0.298"),
    ("1.065", "1.074", "0.297"),
    ("1.074", "1.0832", "0.296"),
    ("1.0832", "1.0917", "0.295"),
    ("1.0917", "1.100", "0.294"),
    ("1.100", "1.108", "0.293"),
    ("1.108", "1.117", "0.292"),
    ("1.117", "1.125", "0.291"),
    ("1.125", "1.134", "0.290"),
    ("1.134", "1.151", "0.288"),
    ("1.151", "1.168", "0.286"),
    ("1.168", "1.184", "0.284"),
    ("1.184", "1.201", "0.282"),
    ("1.201", "1.218", "0.280"),
    ("1.218", "1.250", "0.276"),
    ("1.250", "1.300", "0.270"),
    ("1.300", "1.365", "0.262"),
    ("1.365", "1.465", "0.250"),
    ("1.465", "1.550", "0.240"),
    ("1.550", "1.640", "0.230"),
    ("1.640", "1.740", "0.220"),
    ("1.740", "1.950", "0.200"),
    ("1.950", "2.065", "0.190"),
    ("2.065", "2.100", "0.180"),
]

# Outside [0.47, 2.10], y=0 (x=0) suffices.
# t+1/t decreases up to 1 and increases after 1, so boundary checks
# certify both tails.
tlo, thi = F(47, 100), F(21, 10)
require(
    Q * (tlo + 1 / tlo) > 1,
    "left x=0 tail",
)
require(
    Q * (thi + 1 / thi) > 1,
    "right x=0 tail",
)

# d2(t)=4Qt+2Q/t-2>0 for all t by AM-GM if 8Q^2>1.
require(8 * Q * Q > 1, "positive d2 and d3")

prev = tlo
minimum_bernstein = None

for sa, sb, sy in segments:
    a, b, y = F(sa), F(sb), F(sy)
    require(a == prev and b > a, "contiguous t partition")
    require(2 * y < 1, "exponential certificate range")

    E, O = certificate_polynomials(y)
    coeffs = (
        bernstein_coeffs(E, a, b)
        + bernstein_coeffs(O, a, b)
    )
    require(
        all(z > 0 for z in coeffs),
        "positive Bernstein certificate on "
        + f"[{sa},{sb}] at y={sy}",
    )

    local_min = min(coeffs)
    if (
        minimum_bernstein is None
        or local_min < minimum_bernstein
    ):
        minimum_bernstein = local_min
    prev = b

require(prev == thi, "partition reaches 2.10")

print("PASS exact five-term profile witness")
print("S =", S)
print("H =", H)
print("certified kappa_profile >", float(target))
print("PASS exact full-profile dual ceiling")
print("certified Lambda_profile <=", float(Q))
print("certified kappa_profile <=", sqrt(float(Q)))
print(
    "minimum positive Bernstein coefficient ~",
    float(minimum_bernstein),
)
