"""Rational interval verification of all mixed-envelope imbalanced tails."""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial

ALPHA = F(87, 2000)
BETA = F(11, 2000)
TOTAL = ALPHA+BETA
CUTOFF = 200
POINT_DENOMINATOR = 10**8
LOG_DENOMINATOR = 10**24


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


class I:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = self.lo if hi is None else F(hi)
        require(self.lo <= self.hi, "inverted interval")
    @staticmethod
    def cast(other):
        return other if isinstance(other, I) else I(other)
    def __add__(self, other):
        other = I.cast(other)
        return I(self.lo+other.lo, self.hi+other.hi)
    __radd__ = __add__
    def __neg__(self):
        return I(-self.hi, -self.lo)
    def __sub__(self, other):
        return self+-I.cast(other)
    def __rsub__(self, other):
        return I.cast(other)+-self
    def __mul__(self, other):
        other = I.cast(other)
        vals = [self.lo*other.lo, self.lo*other.hi, self.hi*other.lo, self.hi*other.hi]
        return I(min(vals), max(vals))
    __rmul__ = __mul__
    def __truediv__(self, other):
        other = I.cast(other)
        require(other.lo > 0 or other.hi < 0, "division by interval containing zero")
        return self*I(1/other.hi, 1/other.lo)
    def __rtruediv__(self, other):
        return I.cast(other)/self
    def __pow__(self, power):
        require(power >= 0 and isinstance(power, int), "unsupported interval power")
        if power == 0:
            return I(1)
        if self.lo >= 0:
            return I(self.lo**power, self.hi**power)
        if self.hi <= 0:
            values = [self.lo**power, self.hi**power]
            return I(min(values), max(values))
        if power % 2:
            return I(self.lo**power, self.hi**power)
        return I(0, max(abs(self.lo), abs(self.hi))**power)


def outward(lo, hi):
    q = LOG_DENOMINATOR
    lower = (lo.numerator*q)//lo.denominator
    upper = -((-hi.numerator*q)//hi.denominator)
    return I(F(lower, q), F(upper, q))


def small_log(x):
    require(1 <= x <= 2, "small logarithm outside range")
    z = (x-1)/(x+1)
    terms = 28
    lower = 2*sum((z**(2*j+1)/(2*j+1) for j in range(terms)), F(0))
    tail = 2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
    return outward(lower, lower+tail)


LOG_TWO = small_log(F(2))


@lru_cache(maxsize=50000)
def log_bounds(x):
    x = F(x)
    require(x > 0, "nonpositive logarithm")
    power = 0
    while x >= 2:
        x /= 2
        power += 1
    while x < 1:
        x *= 2
        power -= 1
    result = small_log(x)+power*LOG_TWO
    return outward(result.lo, result.hi)


@lru_cache(maxsize=200)
def log_g_minus_r(r):
    value = r*log_bounds(F(r))-sum((log_bounds(F(k)) for k in range(1, r+1)), I(0))-r
    return outward(value.lo, value.hi)


def coefficients(r, z):
    """G2=a*h^2+b*h*j+c*j^2; G4=a4*h^4+d4*j^4."""
    p2 = (1+r*z)**2*(1+(r+1)*z)
    p4 = (1+r*z)*(1+(r+1)*z)**3
    s2 = 3+(3*r+2)*z+r*(r+1)*z**2
    s4 = 4+(6*r+9)*z+(4*r*r+9*r+6)*z**2+(r+1)**3*z**3
    a = F(1, r+1)-r*r*z**3/p2
    b = -2*r*z*(1+z)/p2
    c = r*(1+z)*s2/p2
    a4 = F(1, (r+1)**3)-r*z**4/p4
    d4 = r*(1+z)*s4/p4
    return a, b, c, a4, d4


def parabola_box(g, curvature, lower, upper):
    """Sup g*x-ALPHA*curvature*x^2 for interval g and lower<=x<=upper."""
    require(curvature > 0 and lower <= 0 <= upper, "invalid strong-concavity parameters")
    maxima = [F(0)]
    for coefficient, left, right in [(g.lo, lower, F(0)), (g.hi, F(0), upper)]:
        location = coefficient/(2*ALPHA*curvature)
        location = min(right, max(left, location))
        maxima.append(coefficient*location-ALPHA*curvature*location*location)
    return max(maxima)


def tail_bound(r, left, right, h, j):
    require(1 <= r < CUTOFF and 0 <= left < right <= F(1, CUTOFF), "tail cell outside coverage")
    require(2 <= h <= r+1 and 0 <= j <= 1, "tail point outside state box")
    z = I(left, right)
    a, b, c, a4, d4 = coefficients(r, z)
    require(a.lo > 0 and a4.lo > 0 and d4.lo > 0, "nonpositive potential coefficient enclosure")
    mh = a.lo/2
    largest_b_squared = max(b.lo*b.lo, b.hi*b.hi)
    mj = c.lo-largest_b_squared/(2*a.lo)
    if mj <= 0:
        return None
    first = h+r*(1+z)*j
    second = 1+r*z
    value_upper = (log_g_minus_r(r).hi+log_bounds(first.hi).hi
                   -log_bounds(second.lo).lo/2
                   -ALPHA*(a*h*h+b*h*j+c*j*j).lo
                   -BETA*(a4*h**4+d4*j**4).lo+TOTAL)
    gh = 1/first-ALPHA*(2*a*h+b*j)-BETA*4*a4*h**3
    gj = r*(1+z)/first-ALPHA*(b*h+2*c*j)-BETA*4*d4*j**3
    correction = parabola_box(gh, mh, F(2)-h, F(r+1)-h)
    correction += parabola_box(gj, mj, -j, F(1)-j)
    return value_upper+correction


def cell_endpoints(index, depth):
    return F(index, CUTOFF*2**depth), F(index+1, CUTOFF*2**depth)
