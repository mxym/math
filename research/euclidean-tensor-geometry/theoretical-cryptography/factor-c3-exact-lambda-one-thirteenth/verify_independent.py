#!/usr/bin/env python3
"""Independent generation by three local Korselt congruences."""
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, lcm, prod


def is_prime(n):
    if n < 2 or n % 2 == 0:
        return n == 2
    t = 3
    while t * t <= n:
        if n % t == 0:
            return False
        t += 2
    return True


def local_residue(a, b, c):
    return (-(b + c) * pow(b*c, -1, a)) % a if a > 1 else 0


def crt_residue(abc):
    size = prod(abc)
    coeff = 0
    for i, a in enumerate(abc):
        if a == 1:
            continue
        b, c = abc[:i] + abc[i+1:]
        m = size // a
        coeff += local_residue(a, b, c) * m * pow(m, -1, a)
    return coeff % size


def main():
    examples = set()
    bound_checks = multidigit = rounding = 0
    for a, b, c in combinations(range(1, 23), 3):
        if gcd(a,b) != 1 or gcd(b,c) != 1 or gcd(a,c) != 1:
            continue
        abc = (a,b,c)
        L = prod(abc)
        for k in range(6):
            g = crt_residue(abc) + k * L
            if g < 2 or g % 2:
                continue
            ps = tuple(1 + g*t for t in abc)
            if not all(map(is_prime, ps)):
                continue
            R = prod(ps)
            lam = lcm(*(p-1 for p in ps))
            assert R not in examples
            examples.add(R)
            assert lam == L*g and all((R//p-1)%(p-1) == 0 for p in ps)
            assert gcd(R, lam) == 1
            S, residue = divmod(R-1, lam)
            assert residue == 0 and isqrt(S) == g == isqrt(S-1)
            J = S-g*g
            x = Fraction(g,J)
            E = (R-1-g**3*L)//g
            assert 1 <= J <= 2*g and x < a < Fraction(9,2)*x
            assert E == L*J
            e1,e2 = sum(abc), a*b+a*c+b*c
            assert (e1-E)%g == 0 and 0 < e1 < 3*L/x**2
            assert E == e1+g*e2
            assert all(t**3-e1*t*t+e2*t-L == 0 for t in abc)
            multidigit += e1 > g
            if a == 1 or b >= 2*a*a:
                assert -(-x.numerator//x.denominator) == a
                rounding += 1
            if g**13 <= R**2*J**13:
                assert x**13 <= R**2
            else:
                assert (Fraction(R,1)/x**6)**13 < R
            bound_checks += 1
            for exponents in [(1,2,3), (3,1,2), (5,4,2)]:
                n = prod(p**i for p,i in zip(ps,exponents))
                powers = lcm(*(p**(i-1)*(p-1) for p,i in zip(ps,exponents)))
                assert gcd(n,powers) == n//R
                assert powers//(n//R) == lam
    assert examples and multidigit and rounding
    # Non-simple and outside the three GSV general size regions by
    # alpha_r < 3/8, alpha_q < 1/3, alpha_p > 1/4.
    R=252601
    assert R == 41*61*101 and R in examples
    assert 101**8 < R**3 and 61**3 < R and 41**4 > R
    print("independent CRT C3 fixtures / bound checks:", len(examples), bound_checks)
    print("nonleast-residue e1 / exact rounding window:", multidigit, rounding)
    print("independent odd-power reductions:", 3*bound_checks)
    print("PASS")


if __name__ == "__main__":
    main()
