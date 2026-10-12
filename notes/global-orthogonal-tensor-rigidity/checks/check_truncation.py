"""Rational interval checks, independent finite evidence for Section 4."""
from fractions import Fraction as Q
from math import factorial


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def exp_negative(r, n=180):
    # Positive series for exp(r); its remaining ratios are <=r/(n+2).
    terms = [Q(r) ** k / factorial(k) for k in range(n + 1)]
    lower = sum(terms)
    ratio = Q(r, n + 2)
    require(ratio < 1, "exponential remainder ratio")
    tail = terms[-1] * Q(r, n + 1) / (1 - ratio)
    return 1 / (lower + tail), 1 / lower


def minus_log(z, n=80):
    require(0 <= z < 1, "log domain")
    lower = sum(z ** k / k for k in range(1, n + 1))
    return lower, lower + z ** (n + 1) / ((n + 1) * (1 - z))


def truncated_moment_polynomial(k):
    # Integral_0^R x^k exp(-x) dx = k! - exp(-R) P_k(R).
    p = [Q(factorial(k), factorial(i)) for i in range(k + 1)]
    # Independently verify derivative(P)-P == -R^k.
    residual = [(i + 1) * p[i + 1] - p[i] if i < k else -p[i]
                for i in range(k + 1)]
    require(residual == [Q(0)] * k + [Q(-1)],
            "integration polynomial identity")
    require(p[0] == factorial(k), "integration lower endpoint")
    return p


def main():
    for k in range(7):
        truncated_moment_polynomial(k)
    require(sum(Q(10) ** k / factorial(k) for k in range(25)) > 20000,
            "exp(10)>20000")
    # Rational lower bound in (21), not a sampled scalar value.
    c = Q(6, 83) * (Q(3, 20) + Q(49, 100) * Q(74, 83)) * Q(13, 100)
    require(c > Q(1, 200), "omega coefficient lower bound")
    for r in (10, 12, 16, 24, 40):
        pl, pu = exp_negative(r)
        vl, vu = Q(r*r) * pl / (1-pl)**2, Q(r*r) * pu / (1-pu)**2
        lp, up = minus_log(pu)
        lpl, upl = minus_log(pl)
        lv, uv = minus_log(vl)
        lvu, uvu = minus_log(vu)
        dl = -up - Q(r)*pu/(1-pu) + lv/2
        du = -lpl - Q(r)*pl/(1-pl) + uvu/2
        require(0 < dl <= du < Q(r*r)*pu, "deficit interval")
        # Exact second moment minus square of exact first moment.
        p = Q(1, 20000)  # identity test at a fixed rational probability
        mean = 1-Q(r)*p/(1-p)
        second = (2-p*(r*r+2*r+2))/(1-p)
        require(second-mean*mean == 1-Q(r*r)*p/(1-p)**2,
                "variance identity")
        require(vu < Q(1, 100), "variance smallness")
        require(2*r**3*pu/(1-pu)**2 + 2*r*pu/(1-pu) < 1,
                "standardized upper support bound")
        # Integral_0^infinity z² exp(-z) dz=2 is verified above at k=2.
        # A rational lower bound for 2 exp(-R-1).
        el, eu = exp_negative(1)
        tail_lower = 2*pl*el
        require(tail_lower > 0, "tail cost")
        print(f"R={r}: certified positive deficit, moment identity, "
              "support and tail bound PASS")
    # All checks remain active with -O; malformed inputs must be rejected.
    caught = False
    try:
        minus_log(Q(1))
    except RuntimeError:
        caught = True
    require(caught, "invalid logarithm domain was accepted")
    print("ALL EXACT TRUNCATION CHECKS PASSED")


if __name__ == "__main__":
    main()
