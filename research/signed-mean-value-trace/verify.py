"""Exact finite checks of the signed trace identities; these are not the proofs.

A symmetric two-by-two matrix is (u,v,w) = [[u+v,w],[w,u-v]].
All spectra and rotations below are rational, except for a common log(2)
scale on H. A rational lower bound from the atanh series certifies the
checks involving log(2). No external packages; checks remain active with -O.
"""

from fractions import Fraction as F
from itertools import product


def require(ok, note):
    if not ok:
        raise ArithmeticError(note)


def diff(x, y):
    return tuple(a-b for a, b in zip(x, y))


def trprod(x, y):
    return 2*sum(a*b for a, b in zip(x, y))


def spectrum(lo, hi, z, x):
    """Return the matrix with eigenvalues lo,hi oriented along (z,x)."""
    lo, hi = F(lo), F(hi)
    return ((lo+hi)/2, (hi-lo)*z/2, (hi-lo)*x/2)


def signed_squares(y, radius):
    c, z, x = y
    require(radius >= 0 and radius**2 == z*z+x*x, "exact spectrum")
    if not radius:
        return ((max(c, 0)**2, 0, 0), (min(c, 0)**2, 0, 0))
    low, high = c-radius, c+radius
    return (spectrum(max(low,0)**2, max(high,0)**2, z/radius, x/radius),
            spectrum(min(low,0)**2, min(high,0)**2, z/radius, x/radius))


def V(p, q, y, radius):
    plus, minus = signed_squares(y, radius)
    return trprod(p, plus) + trprod(q, minus)


def matrix_cases():
    ell_lower = 2*sum(F(1, (2*j+1)*3**(2*j+1)) for j in range(12))
    count = 0
    rotations = ((F(3,5), F(4,5)), (F(5,13), F(12,13)),
                 (F(4,5), F(3,5)), (F(12,13), F(5,13)))
    for h, m, (c,s) in product((1,2), (-2,-1,0,1,2), rotations):
        z, x = c*c-s*s, 2*c*s
        p = spectrum(F(2)**(-h), F(2)**h, 1, 0)
        q = spectrum(F(2)**(m-h), F(2)**(m+h), z, x)
        h0 = (-F(m), h*(1-z), -h*x)  # H/log(2)
        r0 = 2*h*s
        delta = diff(p,q)
        j0 = trprod(h0,delta)          # J/log(2)
        require(j0 > 0, "positive Jeffreys coefficient")
        require(j0 <= ell_lower*V(p,q,h0,r0), "J <= V(H)")
        for k, (c2,s2), sign in product((-1,0,1), rotations, (-1,1)):
            y = (F(k), sign*(c2*c2-s2*s2), sign*2*c2*s2)
            lhs = max(trprod(y,delta), 0)**2
            require(lhs <= V(p,q,y, F(1))*j0*ell_lower, "directional bound")
            count += 1
    return count


def scalar_cases():
    count = 0
    for q in range(2,102):
        a,b = F(0),F(-1)
        c,s = (F(1),F(1)) if q%2 else (F(-1),F(q))
        d = a-b
        lhs = c*(a**q-b**q)
        rhs = F(q,2)*(abs(a)**(q-1)*(s*max(d,0)**2+max(c,0)**2/s)
                      + abs(b)**(q-1)*(s*min(d,0)**2+min(c,0)**2/s))
        require(lhs == 1 and rhs == (0 if q%2 else F(1,2)), "scalar witness")
        count += 1
    return count


if __name__ == "__main__":
    print("PASS:", matrix_cases(), "exact noncommuting directional cases;")
    print("     ", scalar_cases(), "polynomial counterexample substitutions.")
