"""Rooted rank-32 lattice arithmetic; Python standard library. No graph is assumed."""
from fractions import Fraction as F
from itertools import combinations,product
from math import prod

V=range(14)
E=list((i,j)for i,j in combinations(V,2) if j!=(i^1))
assert len(E)==84
M=lambda i,j:int(j==(i^1))
H=[[3*(i==j)-M(i,j)+F(1,9) for j in V] for i in V]
I=[[(3*(i==j)+M(i,j))*F(1,8)-F(1,64) for j in V]for i in V]
assert all(sum(H[i][k]*I[k][j]for k in V)==(i==j)for i,j in product(V,repeat=2))
assert 4**7*2**6*F(32,9)==F(2**25,9)
# With d_s the pair indicator, invert the projection symbolically for all
# possible overlap and matching incidences (no 84x84 inverse required).
for m,v in product(range(3),repeat=2):
    proj=F(3*m+v,8)-F(2,9)+F(14,81*2)-F(1,64)*(2-F(14,9))**2
    assert 8*(F(1,9)-proj)==2-3*m-v
# Compare the dyadic presentations under x+y,2x+y.
q=lambda x,y: (F(x*x,8)+F(y*y,4))%1
assert (q(1,1),q(2,1),(q(3,2)-q(1,1)-q(2,1))%1)==(F(3,8),F(3,4),0)
assert F(28,32)%1==F(7,8) and F(14,8)%1==F(3,4)
assert {i*i%7 for i in range(1,7)}=={1,2,4} and 6 not in {1,2,4}
assert 4*2160+6*240**2-960*(240-24)==146880
print("84 nonmate pairs; rooted 14-Gram inverse; dyadic and seven forms verified.")
print("Rank-32 scalar: shell 4 = 146880+216*roots; field norm = 112j-4p^2-2q^2.")
