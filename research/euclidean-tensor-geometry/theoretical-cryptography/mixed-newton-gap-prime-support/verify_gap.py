"""Finite exact comparisons for the weighted Newton-gap majorant."""
from math import comb

count = 0
for u in range(2, 10):
    for v in range(1, u+1):
        for C in (2, 3, 5):
            residual = []
            for i in range(u):
                for j in range(v):
                    gap = u*v-v*i-u*j
                    if gap < v:
                        continue
                    c = (-1)**(i+j)*C**(gap//v)
                    assert abs(c)**v <= C**gap
                    residual.append((i,j,c))
            for p in (C+1, 2*C, 10*C+1):
                for q in (1, C, 2*p, p**2+1):
                    Z = max(p**u,q**v)
                    values = [c*p**i*q**j for i,j,c in residual]
                    for val in values:
                        assert p*abs(val) <= C*Z
                        count += 1
                    assert p*abs(sum(values)) <= len(residual)*C*Z

# An exactly attained weighted certificate with non-integer exponent.
u,v,C,i,j,c = 3,2,4,0,1,8
gap = u*v-v*i-u*j
assert gap == 3 and c**v == C**gap
assert all(p*c*q <= C*max(p**u,q**v)
           for p in (5, 8, 31) for q in (2, 5, 19, 173))

# Large raw coefficients remain admissible.
m=64
assert comb(m,m//2)>10**17
for i in range(m):
    assert comb(m,i)**m <= m**(m*(m-i))
assert m*m-2*m >= m
print(f"PASS: {count} exact weighted term comparisons, fractional gap and large raw coefficient")
