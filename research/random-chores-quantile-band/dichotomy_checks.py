"""Exact arithmetic illustrations of the quantile tests, not a test of asymptotic EF."""
from fractions import Fraction as Q
def require(x):
 if not x:raise RuntimeError("check failed")
for s in (1,2,3,5,8):
 for j in range(2,26):
  x=Q(1,2**j);u=x**s;v=(2*x)**s
  require(v/u==2**s and 0<u<=v<=1)
print("120 power-law quantile ratios: F(x)=x^s gives exactly 2^s on this entire test grid.")
# F(x)=2^(1-1/x), x_j=1/(4j+2), so log2(u)=-4j-1 and log2(v)=-2j.
for j in range(1,201):
 x=Q(1,4*j+2);require((1-1/x)==-4*j-1 and (1-1/(2*x))==-2*j)
 u=Q(1,2**(4*j+1));v=Q(1,2**(2*j));m=2**(3*j)
 require(v/u==2**(2*j+1) and m*u==Q(1,2**(j+1)) and m*v==2**j)
 require(m*(v-u)==2**j-Q(1,2**(j+1)))
print("200 nondoubling examples on one fixed law: exact m*u=2^(-j-1), m*v=2^j.")
# For an atomless positive-lower-endpoint example uniform on [1/2,1],
# Q(u)=(1+u)/2.  2 Q(u)>1 and v is identically one.
for j in range(2,62):
 u=Q(1,2**(2*j));x=(1+u)/2;v=Q(1);m=2**j
 require(2*x>1 and v/u==2**(2*j) and m*u==Q(1,2**j) and m*v==2**j)
print("60 positive-lower-endpoint edge cases: v=1, while m*u vanishes.")
