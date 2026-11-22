#!/usr/bin/env python3
"""Exact rational bounds for the fixed angular and sieve constants."""
from fractions import Fraction as Q
from math import factorial

ZERO = Q(0)
ONE = Q(1)

def log_enclosure(x, n=24):
    assert x >= 1
    t = (x - 1)/(x + 1)
    low = 2*sum((t**(2*j+1)/Q(2*j+1) for j in range(n)), ZERO)
    high = low + 2*t**(2*n+1)/(Q(2*n+1)*(1-t*t))
    return low, high

# 0 < H_n - log n - gamma_E < 1/(2n); log 20 = log(5/4)+4 log 2.
H20 = sum((Q(1,n) for n in range(1,21)), ZERO)
gamma_lower = H20 - log_enclosure(Q(5,4))[1] - 4*log_enclosure(Q(2))[1] - Q(1,40)
assert gamma_lower > Q(577,1000)
exp_lower = sum((Q(577,1000)**j/factorial(j) for j in range(9)), ZERO)
assert exp_lower > Q(178,100)

beta, D = Q(1,8), Q(498,1000)
s = D/beta
assert 2 < s < 4
f_lower = 2*Q(178,100)/s*log_enclosure(s-1)[0]
assert f_lower > Q(976,1000)

I2_lower = log_enclosure(Q(7))[0]
assert I2_lower > Q(1945,1000)
steps = 512
step = (Q(1,3) - beta)/steps
I3_lower = ZERO
for i in range(1,steps+1):
    u = beta + i*step
    # Integrand is nonnegative and decreasing on this range.
    I3_lower += step * log_enclosure((1-2*u)/u)[0] / (u*(1-u))

# Direct rational sums above are modest here, but no reported bound uses floats.
assert I3_lower > Q(1211,1000)
marginal_lower = Q(178,100)*beta*Q(976,1000)*Q(3156,1000)
ambient_upper = 1+beta**2/(D-2*beta)**2
assert marginal_lower > Q(685,1000)
assert ambient_upper < Q(1255,1000)
assert 2*marginal_lower-ambient_upper > Q(11,100)
print('Exact certificates passed: marginal > .685, ambient < 1.255, intersection > .110.')

# Sharper one-sided exponential bound on the exact Selberg denominator,
# and the two stronger genuine high-mark / low-rank assemblies.
beta = Q(92,1000)
rho = Q(518,1000)
s = D/beta
t = Q(7,4)
assert s > 4
f2_lower = (2*Q(178,100)*log_enclosure(Q(3))[0] + s-4)/s
h = 24
exp_integral_upper = sum((t**j/(j*factorial(j)) for j in range(1,h+1)), ZERO)
# Each successive term after the first omitted one has ratio at most t/(h+2).
exp_integral_upper += t**(h+1)/((h+1)*factorial(h+1))/(1-t/Q(h+2))
assert 2*exp_integral_upper - t*s < -Q(3579,1000)
exp_positive_lower = sum((Q(3579,1000)**j/factorial(j) for j in range(22)), ZERO)
tail_upper = 1/exp_positive_lower
assert tail_upper < Q(2791,100000)
ambient_2 = 1/(1-tail_upper)
assert ambient_2 < Q(1286,1250)  # 1.0288

def declining_integral_lower(lo, hi, log_argument, n=1024):
    step = (hi-lo)/n
    result = ZERO
    for i in range(1,n+1):
        u = lo+i*step
        result += step*log_enclosure(log_argument(u))[0]/(u*(1-u))
    return result

I2 = log_enclosure((1-beta)/beta)[0]
I2H = log_enclosure((1-beta)*(1-rho)/(beta*rho))[0]
I3 = declining_integral_lower(beta,Q(1,3),lambda u:(1-2*u)/u)
I3H = declining_integral_lower(beta,(1-rho)/2,
                            lambda u:(1-rho-u)*(1-2*u)/(rho*u))
A, AH2, AH = (Q(178,100)*beta*f2_lower * w for w in (
                                            I2+I3, I2H, I2H+I3H))
assert A+AH2 > Q(10317,10000)
assert A+AH2-ambient_2 > Q(29,10000)
assert 2*AH-ambient_2 > Q(63,1000)
print('Exact high-mark certificates passed: high E2 vs E2/E3 > .0029, both high E2/E3 > .063.')
