#!/usr/bin/env python3
"""Exact diagnostic replay for the two-band binary tensor lower family.

Universal scope is proved in paper.md. This checker uses only Fraction and
integer arithmetic in Q(sqrt(2)); it samples every order 10..120 to catch
formula/multiplicity mistakes and separately checks the universal integer
inequalities used in the proof.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import comb


def require(ok, msg):
    if not ok:
        raise RuntimeError(msg)


@dataclass(frozen=True)
class Q2:
    a: F = F(0)
    b: F = F(0)  # a + b sqrt(2)

    @staticmethod
    def c(x):
        return x if isinstance(x, Q2) else Q2(F(x), F(0))

    def __add__(self, other):
        o = self.c(other)
        return Q2(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __neg__(self):
        return Q2(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-self.c(other))

    def __rsub__(self, other):
        return self.c(other) - self

    def __mul__(self, other):
        o = self.c(other)
        return Q2(self.a*o.a + 2*self.b*o.b,
                  self.a*o.b + self.b*o.a)
    __rmul__ = __mul__

    def __truediv__(self, other):
        o = self.c(other)
        den = o.a*o.a - 2*o.b*o.b
        require(den != 0, "division by zero")
        return Q2((self.a*o.a - 2*self.b*o.b)/den,
                  (self.b*o.a - self.a*o.b)/den)

    def __pow__(self, n):
        require(isinstance(n, int) and n >= 0,
                "nonnegative integer exponent")
        out = Q2(F(1))
        for _ in range(n):
            out = out*self
        return out

    def sign(self):
        """Exact sign; only rational squares are used in mixed-sign cases."""
        if self.a == 0 and self.b == 0:
            return 0
        if self.a >= 0 and self.b >= 0:
            return 1
        if self.a <= 0 and self.b <= 0:
            return -1
        aa = self.a*self.a
        bb2 = 2*self.b*self.b
        if self.a > 0 and self.b < 0:
            return 0 if aa == bb2 else (1 if aa > bb2 else -1)
        return 0 if aa == bb2 else (1 if bb2 > aa else -1)

    def __le__(self, other):
        return (self.c(other)-self).sign() >= 0

    def __lt__(self, other):
        return (self.c(other)-self).sign() > 0


S = Q2(F(0), F(1))


def formulas(p):
    # r^2=t_1^2; t_2=-sqrt(2)/p. The nested square root is unnecessary.
    r2 = (Q2(p) + S*(p-1))/(p*p)
    t2 = -S/p
    c1sq = p*p*r2
    c2 = F(p*(p-1), 2)*t2
    require(c1sq + 2*c2 == Q2(p),
            f"boundary cancellation p={p}")

    E = 2*p*r2 + 2*comb(p, 2)*(t2*t2)
    E_closed = 2*(Q2(2*p-1) + S*(p-1))/p
    require(E == E_closed, f"distance formula p={p}")

    # G12 has a common nonzero factor 2*t_1.
    cross_bracket = ((1-t2) + (p-2)*t2
                     - (p-2)*t2 + (t2-1))
    require(cross_bracket == Q2(0), f"G12 cancellation p={p}")

    A = (2*(1-t2)**2 + 2*(p-2)*r2
         + 2*comb(p-2, 2)*(t2*t2))
    B = 8*r2 + 8*(p-2)*(t2*t2)
    P = Q2(3*p*p - 7*p + 8) + S*(p*p-p+2)
    Q = Q2(3*p-4) + S*(p-1)
    require(A == 2*P/(p*p), f"G11 formula p={p}")
    require(B == 8*Q/(p*p), f"G22 formula p={p}")
    require(A.sign() > 0 and B.sign() > 0, f"positive Gram p={p}")

    k2 = c2*c2
    require(k2 <= Q2(comb(p, 2)),
            f"quadratic projection coefficient p={p}")
    if p % 2 == 0:
        n = p//2
        H = Q2(2) + 2*k2 + 2*c1sq
        require(H <= Q2(comb(p, n)),
                f"central projection coefficient p={p}")
        require((2*c2).sign() < 0,
                f"negative side-central coefficient p={p}")
    else:
        require((Q2(1)+c2).sign() < 0,
                f"negative odd cross coefficient p={p}")

    return E, A, B


def universal_gates():
    require((Q2(3) - 2*S).sign() > 0, "2 sqrt(2) < 3")
    require((S-Q2(1)).sign() > 0, "sqrt(2) > 1")

    # D(p)=(p-1)(p-2)(p-3)-24(p+3) is positive at p=10.
    # D(p+1)-D(p)=3(p-1)(p-2)-24 is then positive forever.
    p = 10
    D = (p-1)*(p-2)*(p-3)-24*(p+3)
    require(D > 0, "central binomial base gate")
    require(3*(p-1)*(p-2)-24 > 0,
            "central binomial monotonicity gate")
    require(F(p-1, 2) > 1, "odd-cross sign base gate")

    # kappa^2=(2+sqrt(2))/(2(3+sqrt(2)))=2/7+sqrt(2)/14.
    kappa2 = Q2(F(2, 7), F(1, 14))
    require(2*(Q2(3)+S)*kappa2 == Q2(2)+S,
            "kappa identity")
    old2 = S/4
    require((kappa2-old2).sign() > 0,
            "strict improvement over one-band constant")
    return kappa2


def negative_controls():
    p = 17
    r2 = (Q2(p) + S*(p-1))/(p*p)
    t2 = -S/p
    c1sq = p*p*r2
    c2 = F(p*(p-1), 2)*t2
    require(c1sq + 2*c2 != Q2(p+1),
            "corrupted cancellation accepted")
    P_bad = Q2(3*p*p - 7*p + 9) + S*(p*p-p+2)
    _, A, _ = formulas(p)
    require(A != 2*P_bad/(p*p),
            "corrupted Gram formula accepted")


def main():
    universal_gates()
    for p in range(10, 121):
        formulas(p)
    negative_controls()
    print("Q(sqrt(2)) formulas and projection coefficients, "
          "orders 10..120: EXACT PASS")
    print("Universal p>=10 integer gates: EXACT PASS")
    print("Asymptotic constant identity and strict improvement: EXACT PASS")
    print("Negative controls: PASS")
    print("ALL EXACT DIAGNOSTICS PASSED; universal scope is proved in paper.md")


if __name__ == "__main__":
    main()
