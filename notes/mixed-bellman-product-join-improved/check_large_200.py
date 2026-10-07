#!/usr/bin/env python3
"""Exact rational checks for the r,s >= 200 part of the improved mixed Bellman bound."""
from fractions import Fraction as F


def require(v, msg):
    if not v:
        raise ArithmeticError(msg)

ALPHA = F(271, 6250)
BETA = F(5453, 10**6)
T = ALPHA + BETA
require(T == F(48813, 10**6), 'T mismatch')

# Machin lower bound, identical proof pattern to the audited predecessor.
pi_lo = 16*(F(1,5)-F(1,5)**3/3+F(1,5)**5/5-F(1,5)**7/7)-F(4,239)
require(pi_lo > F(314159,100000), 'pi lower bound unexpectedly weak')

# For r,s >= m, predecessor algebra gives
# C^2/k < (2/3 + 1/m)/pi.  Take m=200.
lhs_upper = (F(2,3) + F(1,200)) / pi_lo
x = 1 - 2*T
require(x == F(451187,500000), 'large exponent mismatch')

# Positive Taylor polynomial is a lower bound for exp(x), x>0.
sm = F(1); term = F(1)
for j in range(1, 8):
    term *= x/j
    sm += term
rhs_lower = 2*ALPHA*sm
require(lhs_upper < rhs_lower, 'large-d closure constant failed')

# Final endpoint exp(1+T) < 2.854262.
y = 1 + T
N = 6
sm2 = F(1); term2 = F(1)
for j in range(1, N+1):
    term2 *= y/j
    sm2 += term2
first_omitted = term2*y/(N+1)
exp_upper = sm2 + first_omitted/(1-y/(N+2))
target = F(1427131,500000)  # 2.854262
require(exp_upper < target, 'final decimal endpoint failed')

# Regression of the nonnegative-square identity used to reduce G2 >= k x^2.
for r,s,h,j in [(200,200,F(1),F(2)),(200,317,F(7,3),F(11,5)),
                (503,811,F(13,7),F(17,9)),(1000,1000,F(6),F(6))]:
    n=r+s; de=4*r*s+3*n+2; k=F(3*n+2,de); B=(s*h+r*j)/n
    G=h*h/(r+1)+j*j/(s+1)-(r*h+s*j)**2/(n*n*(n+1))
    rhs=F(r*s,(r+1)*n*n*(s+1)*(n+1)*de)*((s+1)*(3*r+s+2)*h-(r+1)*(r+3*s+2)*j)**2
    require(G-k*B*B==rhs,'quadratic identity regression failed')

print('PASS: exact large-d closure for r,s >= 200.')
print('PASS: Gamma_C <= exp(1.048813) < 2.854262.')
print('large_margin =', rhs_lower-lhs_upper)
print('endpoint_margin =', target-exp_upper)
