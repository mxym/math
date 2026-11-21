"""Exact rational bounds, also under python -O."""
from fractions import Fraction as Q
from math import factorial
def req(b):
    if not b: raise ValueError("failed certified inequality")
def logs(x):
    x=Q(x);req(x>=1); z=(x-1)/(x+1); n=30
    l=2*sum((z**(2*j+1)/(2*j+1) for j in range(n)),Q())
    return l,l+2*z**(2*n+1)/((2*n+1)*(1-z*z))
def lo(x):return logs(x)[0]
def hi(x):return logs(x)[1]
H=sum((Q(1,j) for j in range(1,4097)),Q())
gam=H-12*hi(2)-hi(Q(4097,4096))  # <= H_4096 - log(4097) < gamma
req(gam>Q(577,1000))
E=sum((Q(577,1000)**j/factorial(j) for j in range(11)),Q())
raw=4*hi(2)-1
req(raw/E<Q(9956,10000))
gap=Q(4,100*factorial(99))
lowerr=300000*gap+Q(702,factorial(300))
cubeerr=8*gap
req(lowerr+cubeerr<Q(1,10**8))
req(1-raw/E-lowerr-cubeerr>Q(43,10000))
print("Upper e^-gamma (4 log 2-1)<0.9956; certified positive margin >0.0043.")
