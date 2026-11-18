"""Exact arithmetic checks for Sec. 3. Does not generate the random matrices."""
from fractions import Fraction as Q
from math import factorial, isqrt

d = 2**40
L = d+1
t = Q(1,16)
log2_lo = 2*(Q(1,3)+Q(1,3)**3/3)
log2_hi = Q(7,10)
assert sum(log2_hi**i/factorial(i) for i in range(4)) > 2
assert log2_lo == Q(56,81)
assert 36*Q(22,7)**3*log2_hi < 1000
assert isqrt(d)**2 == d
assert 1+4*isqrt(d)/t == 1+2**26 < 2**27
logd_hi = 40*log2_hi
assert logd_hi == 28
neg_coeff = d*t*t/(2000*logd_hi**2)
assert neg_coeff > 2000
# ln 3 < 2 since the positive Taylor series for exp(2) exceeds 3.
assert 54*d*log2_hi + L*2-2000*L < 0
gap0 = 2*log2_lo - (Q(1,2)+Q(1,3)+Q(1,4))
assert gap0 == Q(97,324)
assert gap0-logd_hi/L > 4*t == Q(1,4)
assert 2*t == Q(1,8)
print(f'd={d}; L={L}; negative exponent per basis > {neg_coeff} > 2000')
print(f'MUB maximum minus center > {gap0-logd_hi/L} > 1/4 nat')
print('All rational comparisons passed. Existence certificate; no matrix tuple enumerated.')
