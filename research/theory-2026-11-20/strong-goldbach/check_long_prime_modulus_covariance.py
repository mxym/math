"""Exact local/endpoint/control replay, not an analytic proof; run python -O."""
from fractions import Fraction as F
from itertools import product
from math import prod


def need(cond, info):
    if not cond:
        raise ArithmeticError(info)


def c(p, n):
    return p - 1 if n % p == 0 else -1


def s(p, n):
    return F(p * (p - (1 if n % p == 0 else 2)), (p - 1)**2)


def d(p, n):
    return F(1) + F(-c(p, n), (p - 1)**3)


def ell(p, n):
    return F(1, p-2) if n % p == 0 else -F(1, p*p-3*p+3)


def sg3(p, n, h):
    return 1 + F(c(p, n) * c(p, h), (p - 1)**3)


primes = [2, 3, 5, 7, 11, 13, 17, 23, 31, 47]
local_cases = 0
for p in primes:
    for n in range(0, p, 2 if p == 2 else 1):
        for h in range(p):
            count = sum((n + h*z - a) % p != 0
                        for z in range(1, p) for a in range(1, p))
            need(F(p*count, (p-1)**3) == sg3(p, n, h),
                 ("ternary local roots", p, n, h))
            if p == 2:
                need(sg3(p, n, h) == 2*(h % 2 == 0), ("parity", n, h))
            else:
                need(sg3(p, n, h) == (s(p, n) if h % p == 0 else d(p, n)),
                     ("two local values", p, n, h))
                need(d(p, n) * (1 + ell(p, n)) == s(p, n),
                     ("endpoint factor", p, n))
                need(d(p, n) * (1 + ell(p, n)/p) == 1,
                     ("first Euler product", p, n))
            local_cases += 1


def spline(t):
    return max(F(0), 1-t)**2


def spline_sum(t):
    m = int(1/t)
    return F(m) - t*m*(m+1) + t*t*m*(m+1)*(2*m+1)/6


factor_set = [3, 5, 7, 11]
end_cases = 0
for mask in product((False, True), repeat=len(factor_set)):
    n = 2 * prod(p for p, bit in zip(factor_set, mask) if bit)
    D = prod(d(p, n) for p in factor_set)
    singular = 2 * prod(s(p, n) for p in factor_set)
    coefficients = [
        (prod(p for p, bit in zip(factor_set, bits) if bit),
         prod(ell(p, n) for p, bit in zip(factor_set, bits) if bit))
        for bits in product((False, True), repeat=len(factor_set))
    ]
    need(D * sum(F(coef)/h for h, coef in coefficients) == 1, ("main product", n))
    need(2 * D * sum(coef for _, coef in coefficients) == singular,
         ("endpoint product", n))
    for v in [F(1, 9), F(2, 83), F(1, 305), F(3, 1081), F(7, 140)]:
        true = sum(prod(sg3(p, n, h) for p in [2] + factor_set) * spline(h*v)
                   for h in range(1, int(1/v)+1))
        opened = 2*D*sum(coef*spline_sum(2*h*v) for h, coef in coefficients)
        expected = F(1, 3)/v - singular/2  # Here F(v)=(1-v)_+^2, F(0)=1.
        error_bound = 2*D*sum(abs(coef)*min(1, 2*h*v) for h, coef in coefficients)
        need(true == opened, ("switched endpoint equality", n, v))
        need(abs(true-expected) <= error_bound, ("endpoint bound", n, v))
        end_cases += 1

# Independent exact distinction between reflected covariance and alias count.
data = {19: 11, 23: 13, 29: 17, 31: 19, 37: 12, 41: 17, 43: 6, 47: 11}
A = sum(data.values())
cov_cases = 0
for q in [3, 5, 7, 11, 13, 17]:
    A_q = [sum(v for n, v in data.items() if n % q == a) for a in range(q)]
    E = [F(0)] + [a-F(A,q-1) for a in A_q[1:]]
    need(A_q[0] == 0 and sum(E) == 0, ("units", q))
    for n in range(36, 100, 2):
        main = F(q-(1 if n % q == 0 else 2), (q-1)**2)*A*A
        cov = sum(E[a]*E[(n-a) % q] for a in range(q))
        linear = -2*F(A,q-1)*E[n % q]
        congr = sum(aa*bb for a,aa in data.items() for b,bb in data.items()
                    if (a+b-n) % q == 0)
        exact = sum(aa*bb for a,aa in data.items() for b,bb in data.items()
                    if a+b == n)
        aliases = sum(aa*bb for a,aa in data.items() for b,bb in data.items()
                      if (a+b-n) % q == 0 and a+b != n)
        need(congr == exact + aliases == main + cov + linear,
             ("AP centering and aliases", q, n))
        cov_cases += 1
print(f"PASS: {local_cases} local ternary cases, {end_cases} exact endpoint sums, "
      f"{cov_cases} centered-congruence decompositions")
