"""Exact diagnostic replay; the all-real/all-orders proofs are in paper.md/Lean.

Uses only the Python standard library, explicit failures, sparse rational
polynomials, and quadratic-number arithmetic. No optimizer or float is used.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import comb, isqrt
from random import Random


def require(condition, label):
    if not condition:
        raise ValueError(label)


class Poly:
    """Sparse polynomials in three variables over Q."""
    def __init__(self, terms=0):
        if not isinstance(terms, dict):
            terms = {(0, 0, 0): F(terms)}
        self.terms = {e: F(c) for e, c in terms.items() if c}

    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = self.terms.copy()
        for e, c in other.terms.items():
            out[e] = out.get(e, 0) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, Poly) else -F(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                g = tuple(a+b for a, b in zip(e, f))
                out[g] = out.get(g, 0) + c*d
        return Poly(out)

    __rmul__ = __mul__

    def __truediv__(self, other):
        return self * (1/F(other))

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, 'polynomial exponent')
        out = Poly(1)
        for _ in range(exponent):
            out = out*self
        return out

    def __eq__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        return self.terms == other.terms


@dataclass(frozen=True)
class Surd:
    """a+b*sqrt(d); perfect square d is reduced immediately."""
    a: F
    b: F = F(0)
    d: int = 3

    def __post_init__(self):
        require(self.d > 0, 'positive radicand')
        a, b = F(self.a), F(self.b)
        r = isqrt(self.d)
        if r*r == self.d:
            a, b = a+b*r, F(0)
        object.__setattr__(self, 'a', a)
        object.__setattr__(self, 'b', b)

    def coerce(self, other):
        if not isinstance(other, Surd):
            other = Surd(F(other), d=self.d)
        require(self.d == other.d, 'same quadratic arithmetic')
        return other

    def __add__(self, other):
        other = self.coerce(other)
        return Surd(self.a+other.a, self.b+other.b, self.d)

    __radd__ = __add__

    def __neg__(self):
        return Surd(-self.a, -self.b, self.d)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        return Surd(self.a*other.a+self.d*self.b*other.b,
                    self.a*other.b+self.b*other.a, self.d)

    __rmul__ = __mul__

    def __truediv__(self, other):
        return Surd(self.a/F(other), self.b/F(other), self.d)

    def __pow__(self, exponent):
        out = Surd(F(1), d=self.d)
        for _ in range(exponent):
            out = out*self
        return out


def scalar_certificate():
    u = Poly({(1, 0, 0): 1})
    v = Poly({(0, 1, 0): 1})
    s = Poly({(0, 0, 1): 1})
    t = (v-u)/6
    k = (4-v*v)/16

    def defect(z):
        return (3*z+12*t*t-12*u*t*z-48*u*t**3
                -(48+36*u*u)*t*t*z-(4+12*u*u)*z*z-96*t**4)

    zero = 12*t*t*(F(4, 9)*(u-v/4)**2+1-v*v/4)
    top = (16*(4*u-v)**2*(u-v)**2
           +27*(1-u*u)*(4-v*v)*(4*u*u-8*u*v+v*v+8))/1728
    require(defect(0) == zero, 'quartic endpoint zero')
    require(defect(k) == top, 'quartic endpoint cap')
    require(k*defect(s) == (k-s)*zero+s*top+(4+12*u*u)*k*s*(k-s),
            'quartic interpolation')
    require(4*u*u-8*u*v+v*v+8 == (2*u-v)**2+4*(2-u*v), 'Q factor')
    residual = ((F(1, 2)-2*u*t+2*t*t+2*s*(1-u*u))*(2*s+8*t*t)
                -4*t*t*s*(1-u*u))
    require(3*residual-4*(2*s+6*t*t)**2 == defect(s), 'residual link')
    require(defect(k) != top+1, 'negative control: corrupted polynomial rejected')
    print('Quartic endpoint/interpolation/residual identities: EXACT PASS')


def norm(t):
    p = len(t)-1
    return sum(comb(p, k)*x*x for k, x in enumerate(t))


def gram(t):
    p = len(t)-1
    a = sum(comb(p-2, k)*(t[k]-t[k+2])**2 for k in range(p-1))
    b = 4*sum(comb(p-2, k)*t[k+1]**2 for k in range(p-1))
    c = 2*sum(comb(p-2, k)*(t[k]-t[k+2])*t[k+1] for k in range(p-1))
    return a, b, c


def ordered_residual(t):
    p = len(t)-1
    labels = list(product((0, 1), repeat=p-2))
    matrices = []
    for alpha in labels:
        k = sum(alpha)
        matrices.append([[t[k], t[k+1]], [t[k+1], t[k+2]]])
    total = 0
    for x in matrices:
        for y in matrices:
            for i in range(2):
                for j in range(2):
                    c = sum(x[i][r]*y[r][j]-y[i][r]*x[r][j] for r in range(2))
                    total += c*c
    return total


def rotate(t, q):
    """Substitute x=q00 X+q01 Y, y=q10 X+q11 Y in the binary form."""
    p = len(t)-1
    out = [0 for _ in t]
    for k, coeff in enumerate(t):
        for i in range(p-k+1):
            for j in range(k+1):
                out[i+j] += (comb(p, k)*coeff*comb(p-k, i)*comb(k, j)
                             *q[0][0]**(p-k-i)*q[0][1]**i
                             *q[1][0]**(k-j)*q[1][1]**j)
    return [x/comb(p, k) for k, x in enumerate(out)]


def tensor_checks():
    rng = Random(20261007)
    q = [[F(3, 5), F(4, 5)], [F(-4, 5), F(3, 5)]]
    for p in range(3, 15):
        for _ in range(20):
            t = [F(rng.randint(-4, 4), rng.randint(1, 5)) for _ in range(p+1)]
            a, b, c = gram(t)
            trace = sum(comb(p-2, k)*(t[k]+t[k+2])**2 for k in range(p-1))
            require(a+b == 2*norm(t)-trace, 'Gram trace identity')
            require(3*trace <= 4*norm(t), 'all-order cubic trace bound')
            rot = rotate(t, q)
            aa, bb, cc = gram(rot)
            require(norm(rot) == norm(t), 'rotation norm')
            require(aa+bb == a+b and aa*bb-cc*cc == a*b-c*c, 'Gram invariants')
            if p <= 7:
                require(ordered_residual(t) == a*b-c*c, 'complete ordered residual')
    rt = Surd(F(0), F(1))
    t = [Surd(F(4)), rt, Surd(F(0)), rt, Surd(F(4))]
    a, b, c = gram(t)
    require(norm(t) == Surd(F(56)), 'sharp quartic norm')
    require((a, b, c) == (Surd(F(32)), Surd(F(24)), Surd(F(0))), 'sharp quartic Gram')
    require(ordered_residual(t) == Surd(F(768)), 'sharp quartic ordered residual')
    require(norm(t)-32 == Surd(F(24)), 'sharp quartic distance with paper maximum certificate')
    require(4*(norm(t)-32)**2 == 3*(a*b-c*c), 'sharp equality')
    require(ordered_residual(t) != Surd(F(384)), 'negative control: missing ordered pairs')
    print('Complete ordered contractions, Gram covariance, sharp quartic Q(sqrt(3)): EXACT PASS')


def growth_family():
    x, y = Poly({(1, 0, 0): 1}), Poly({(0, 1, 0): 1})
    # Coefficients of the two squared evaluations are expanded separately
    # in the quadratic field; no square root or numerical maximization.
    for p in range(5, 41):
        t = [Surd(F(0), d=p) for _ in range(p+1)]
        t[0] = t[p] = Surd(F(1), d=p)
        t[1] = t[p-1] = Surd(F(0), F(1, p), p)
        a, b, c = gram(t)
        require(norm(t) == Surd(F(4), d=p), 'growth-family norm')
        require((a, b, c) == (Surd(F(4*(p-1), p), d=p),
                             Surd(F(8, p), d=p), Surd(F(0), d=p)), 'growth-family Gram')
        # f=A+sqrt(p) B. Square each real polynomial and substitute p for sqrt(p)^2.
        A = x**p+y**p
        B = x**(p-1)*y+x*y**(p-1)
        Av = (-y)**p+x**p
        Bv = (-y)**(p-1)*x+(-y)*x**(p-1)
        rational_part = A*A+Av*Av+p*(B*B+Bv*Bv)
        root_part = 2*(A*B+Av*Bv)
        base = x**(2*p)+y**(2*p)+p*(x*x*y**(2*p-2)+y*y*x**(2*p-2))
        if p % 2:
            require(rational_part == 2*base, 'odd projection rational part')
            require(root_part == 4*(x*y)**(p-1)*(x*x+y*y), 'odd projection root part')
            coefficient = comb(p, (p-1)//2)
            require(coefficient*coefficient >= 4*p, 'odd central coefficient')
        else:
            require(rational_part == 2*base+4*(p+1)*(x*y)**p, 'even projection rational part')
            require(root_part == 0, 'even projection root cancellation')
            require(comb(p, p//2) >= 2*(p+1), 'even central coefficient')
        # Independently replay the exact trace singular-value ratio.
        for r in range(1, p):
            ratio = F(2*r*(p-r), p*(p-1))**2 * F(comb(p, r), comb(p-2, r-1))
            require(ratio == F(4*r*(p-r), p*(p-1)), 'trace singular value')
    print('Orders 5..40: growth-family Gram, projection polynomial, binomial and trace identities EXACT PASS')


if __name__ == '__main__':
    scalar_certificate()
    tensor_checks()
    growth_family()
    print('ALL EXACT CHECKS PASSED (finite diagnostics; see written/Lean proofs for universal scope)')
