"""Exact lower enclosures for the two signed angular credits."""
from fractions import Fraction as Q

def need(b):
    if not b:
        raise ArithmeticError("failed rational certificate")

def log63(x):
    t=(x-1)/(x+1)
    n=32
    v=2*sum((t**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
    err=2*abs(t)**(2*n+1)/(Q(2*n+1)*(1-t*t))
    return v-err,v+err

rho=Q(2501,10000)
b=1-2*rho
B2_low=2*log63(2*(1-rho))[0]
Ll,Lu=log63(1/b)  # magnitude of log b
B3_low=Q(0)
for i in range(8):
    j=i+1
    if i%2 == 0:
        B3_low+=2*b**j*(Ll/j+Q(1,j*j))
    else:
        B3_low-=2*b**j*(Lu/j+Q(1,j*j))
need(B2_low>Q(810,1000))
need(B3_low>Q(1458,1000))
need(B2_low+B3_low>Q(2268,1000))
# Euler's sum with an integral lower bound on its omitted tail.
n=128
zeta2_low=sum((Q(1,j*j) for j in range(1,n+1)),Q(0))+Q(1,n+1)
need(zeta2_low>Q(16449,10000))
need(1+zeta2_low-Q(1,1000)>Q(26439,10000))
print("rank-two and rank-three angular credits, strict dyadic threshold verified")
