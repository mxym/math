from math import comb
from fractions import Fraction as F

m, grid = 12, 4000
target = F(12865, 10000)**2
coef = [F(comb(4*k, 2*k)*comb(2*k, k), (4*k-1)*64**k) for k in range(1, m+1)]
if not sum(coef) < 1:
    raise ArithmeticError("upper polynomial not certified positive")
for i in range(grid):
    x2 = F(i, grid)**2
    q = F(0)
    for c in reversed(coef):
        q = (q + c)*x2
    if (1+F(i+1, grid))*(1-q)**2 >= target:
        raise ArithmeticError(f"interval {i} failed")
print("PASS F_2(x)<1.2865 for all x in [0,1]")
