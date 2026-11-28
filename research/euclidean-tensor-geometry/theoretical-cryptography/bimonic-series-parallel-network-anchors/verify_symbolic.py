#!/usr/bin/env python3
"""Exact algebraic checks on fixed synthetic fixtures. No inputs."""
import sympy as S

T, U, Y = S.symbols("T U Y")
f1, f2, f3, h = 2*T+1, 3*T-4, T+6, 4*T+3
A, B = (U-f1)*(U-f2), (U-f1)*(U-f3)
C = (3*Y-4*U-25)*(Y-4*U+21)
D = Y-h
g = S.gcd(A, B, U)
assert S.expand(g-(U-f1)) == 0
sp = S.resultant(g, C, U)
assert S.degree(sp, Y) == 2
assert S.gcd(sp, D, Y) == 1
r = S.resultant(sp, D, Y)
assert S.expand(r+16*(T-5)**2) == 0
assert S.degree(S.gcd(S.resultant(A, C, U), D, Y), Y) == 1
assert S.degree(S.gcd(S.resultant(B, C, U), D, Y), Y) == 1
assert S.expand(sp.subs(Y, h)+16*(T-5)**2) == 0
assert S.solve([A, B, C, D], (T, U, Y)) == [(5, 11, 23)]

# Verify meaningful specialization failure and a right-child pullback.
P, Q = (Y-T)*(Y-2*T-1), (Y-T)*(Y-3*T+1)
K = S.QQ.frac_field(T)
p, q = S.Poly(P, Y, domain=K), S.Poly(Q, Y, domain=K)
a, b, g = S.gcdex(p, q)
assert a*p+b*q == g == S.Poly(Y-T, Y, domain=K)
assert S.expand(g.as_expr().subs(T, 2)) == Y-2
assert S.expand(S.gcd(P.subs(T, 2), Q.subs(T, 2))-(Y-2)*(Y-5)) == 0
pull = S.resultant(U-2*T-1, U-2, U)
assert S.expand(pull-(2*T-1)) == 0
assert S.resultant(U**2+U-T, U-2, U) == 6-T

# Simultaneous parallel empty child can specialize to a nonempty child.
p0, q0 = Y-T, Y-2*T+2
assert S.gcd(p0, q0, Y) == 1
assert S.resultant(p0, q0, Y) == 2-T
assert S.gcd(p0.subs(T, 2), q0.subs(T, 2), Y) == Y-2

# Constant leading coefficients protect every point even with repeated roots.
leaf = (Y-2*U-1)**2
path = S.resultant(U**2-T, leaf, U)
assert S.expand(path-((Y-1)**2-4*T)**2) == 0
for t in (0, 1, 9, -1, S.Rational(1, 4)):
    direct = {2*u+1 for u in S.solve(U**2-t, U)}
    got = set(S.solve(path.subs(T, t), Y))
    assert got == direct
print("PASS: shared-variable anchor, gcd jump, local pullbacks, and 5 exact path specializations")
