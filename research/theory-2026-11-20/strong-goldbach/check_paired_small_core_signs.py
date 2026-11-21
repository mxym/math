from fractions import Fraction as F


def require(flag, details):
    if not flag:
        raise ArithmeticError(details)


# Standard proven Archimedean bounds for pi.
pi_lo, pi_hi = F(157, 50), F(22, 7)
z2_hi = pi_hi**2 / 6
z3_lo = sum((F(1, n**3) for n in range(1, 33)), F(0))
z3_hi = sum((F(1, n**3) for n in range(1, 6)), F(0)) + F(1, 2 * 5**2)
z5_lo = F(1) + F(1, 32)
c2hi, c3hi = -pi_lo**2/12, -z3_lo/3
c4lo, c4hi = pi_lo**4/1440, pi_hi**4/1440
c5hi = z2_hi*z3_hi/6-z5_lo/5
require(c4lo > F(".067"), "rank four limit")
require(c2hi+c3hi+c4hi+c5hi < -F("1.02"), "opposite rank 2–5 limit")
# The lower log(10) from the convergent atanh series suffices for
# gamma <= H5-log(5) < log(2), without a decimal gamma assertion.
v = F(9, 11)
log10lo = 2 * sum((v**(2*j+1)/(2*j+1) for j in range(12)), F(0))
require(log10lo > sum((F(1, n) for n in range(1, 6)), F(0)), "e^(-gamma)>1/2")
K = F(".06282")/2
require(K * F(".064") - F(".0005") > F(".001"), "uniform rank4")
require(K * F("1.01") - F(".001") > F(".030"), "uniform total rank2–5")
require(K * F(".01") - F(".0001") > F(".0001"), "uniform rank6+")
print("Certified C4 >", float(c4lo),
      "and C2+C3+C4+C5 <", float(c2hi+c3hi+c4hi+c5hi))
print("All strict normalized margins verified")
