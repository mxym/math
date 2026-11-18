from fractions import Fraction as Q
from math import factorial, isqrt
def ck(x):
    if not x: raise RuntimeError("arithmetic check failed")
d=2**40;L=d+1;T=40000
# e^11>40000 by direct truncated exponential.
ck(sum(Q(11)**k/factorial(k) for k in range(20))>T)
ck(T*T+2*T+3 < Q(2)**T/1000)
for lam,a,V,ub in [(Q(1,100000),Q(9,1000),2,T),(Q(1,500000),Q(1,40),29,11*T+6)]:
    ck(lam*ub<=1)
    ck(d*(lam*a-lam*lam*V)>50000)
# d e^{-1000}+4 e^{-11000}<1
ck(Q(d,2**1000)+Q(4,2**11000)<1)
ck(Q(16,isqrt(d))+Q(116,d)<Q(1,1000))
ck(Q(5,99)<Q(1,19))
ck(1+400*isqrt(d) < 2**29)
ck(58*d+L < 78*L)  # ln(2)<1
ck(Q(1,19)+Q(29,500)+Q(1,100)+Q(1,1000)<Q(1,8))
# Extra independent MUB-gap lower bound: use monotonicity g_d and d=8,
# and positive-series lower estimate ln 2 > 2(1/3 + 1/81).
ln2lower=2*(Q(1,3)+Q(1,81))
h8=sum(Q(1,k) for k in range(1,9))
ck(3*ln2lower-h8+1-Q(40,d+1)>Q(1,4))
print("Independent finite elementary exponent, net, center and MUB comparisons all passed.")
