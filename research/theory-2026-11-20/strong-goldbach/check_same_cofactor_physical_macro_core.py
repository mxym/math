from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt


def require(flag, details):
    if not flag:
        raise ArithmeticError(details)


@lru_cache(None)
def factors(n):
    out = {}
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            j = 0
            while n % p == 0:
                j += 1
                n //= p
            out[p] = j
    if n > 1:
        out[n] = 1
    return out


@lru_cache(None)
def divisors(n):
    ds = [1]
    for p, j in factors(n).items():
        ds = [d * p**i for d in ds for i in range(j + 1)]
    return ds


@lru_cache(None)
def mu(n):
    fs = factors(n)
    return 0 if any(j > 1 for j in fs.values()) else (-1)**len(fs)


def short(n, U):
    return sum(mu(d) for d in divisors(n) if d <= U)


def clean(d):
    return {k: v for k, v in d.items() if v}


counts = dict(total=0, small_long=0, repeated_macro=0,
              no_macro=0, one_macro=0, mixed_core_zero=0, squarefree_pure=0)
for U in [2, F(7, 2), 5, 11, F(33, 2), 47]:
    for n in range(1, 3601):
        left, right = defaultdict(int), defaultdict(int)
        fs = factors(n)
        v = 1
        for p, j in fs.items():
            if p <= U:
                v *= p**j
        macro = [p for p in fs if p > U]
        counts['no_macro'] += not macro
        counts['one_macro'] += len(macro) == 1
        counts['repeated_macro'] += any(fs[p] > 1 for p in macro)
        if len(fs) == 1 and n > U:
            right[next(iter(fs))] += 1
        for p, j in fs.items():
            for i in range(1, j + 1):
                ell = p**i
                if ell > U:
                    left[p] += sum(mu(d) for d in divisors(n // ell) if d > U)
                    if p <= U:
                        right[p] -= short(v // ell, U)
                        counts['small_long'] += 1
            if p > U:
                right[p] -= j * short(v, U)
        require(clean(left) == clean(right), (n, U, left, right))
        if macro and 1 < v <= U:
            require(not clean(left), (n, U, "nonprime short core block"))
            counts['mixed_core_zero'] += 1
        if v == 1 and len(fs) >= 2 and all(j == 1 for j in fs.values()):
            require(clean(left) == {p: -1 for p in fs}, (n, U, "pure ridge"))
            counts['squarefree_pure'] += 1
        counts['total'] += 1

eps = F(".49")
require(1 - eps > F("0.50"), "e cutoff BV reserve")
harmonic_a = 1 - eps - F(1, 4)
power = 1 - F(5, 4) + harmonic_a - 3 * eps
require(power == -F("1.46"), ("quarter neck", power))
require(F(".14") + 3 * F(".25") + F(".01") == F(".90"), "fixed labels and floor")
print(counts)
print("quarter neck x L^", power, "; BV subpower exponent", 1 - eps)
