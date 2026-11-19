"""Exact finite checks of the rounded sign count AND target; not a cutoff proof."""
from fractions import Fraction
from math import comb, gcd


def prediction(r, s, n):
    d = s - 2*r
    center = Fraction(6*n, 5*d) + Fraction(2*(120*d*d + 95*s*s - 296), 125*d*(d*d-s*s))
    first = pow(r, -1, s)
    j = (center - first) / s
    if j - int(j // 1) == Fraction(1, 2):
        raise ArithmeticError("arithmetic separation fails")
    t = first + s*((j + Fraction(1, 2)) // 1)
    x, rem = divmod(r*t-1, s)
    if rem:
        raise ArithmeticError("wrong congruence")
    return t, x


def observed(r, s, n):
    """Scale by s**n. P[j] = mass at j-(n-ell) for ell plus signs."""
    q = s-r
    P = [comb(n, j)*r**(n-j)*q**j for j in range(n+1)]
    best, winners = 0, []
    norm = s**n
    for ell in range(n+1):
        if min(P) <= 0 or sum(P) != norm:
            raise ArithmeticError("not a probability polynomial")
        if 2*ell >= n:
            h = max(P)
            if h > best:
                winners.clear()
                best = h
            if h == best:
                winners.extend((2*ell-n, j-(n-ell)) for j, mass in enumerate(P) if mass == h)
        if ell == n:
            break
        # Exact multiplication by (q + r*z)/(r + q*z).
        prev, new = 0, []
        for j in range(n):
            val, rem = divmod(P[j] - q*prev, r)
            if rem:
                raise ArithmeticError("polynomial division failed")
            new.append(q*val + r*prev)
            prev = val
        if P[-1] != q*prev:
            raise ArithmeticError("leading term did not divide")
        P = new+[r*prev]
    return winners


def main():
    tests = 0
    for r, s in [(1,4),(1,6),(3,8),(1,8),(3,10),(5,12),(5,14)]:
        period = 5*(s-2*r)*s // gcd(5*(s-2*r)*s, 6)
        for n in (201,203,205,251,401,501):
            t, x = prediction(r, s, n)
            if observed(r, s, n) != [(t, x)]:
                raise ValueError((r, s, n, t, x))
            if prediction(r, s, n+period)[0] - t != Fraction(6*period, 5*(s-2*r)):
                raise ArithmeticError("period mismatch")
            tests += 1
            print(f"p={r}/{s} n={n}: t={t} x={x} period={period}")
    print(f"PASS: {tests} exact full-law comparisons; finite consistency checks only.")


if __name__ == "__main__":
    main()
