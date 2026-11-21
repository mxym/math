#!/usr/bin/env python3
"""Rational certificate for the hybrid low-marker all-small tail at alpha=.155."""
from fractions import Fraction as F
from math import factorial,comb
from pathlib import Path
from runpy import run_path

d=run_path(str(Path(__file__).with_name('check_cubic_even_tail.py')))
a=F(31,200)
def req(cond,msg):
    if not cond: raise ArithmeticError(msg)
# Rank 8: remove one smallest coordinate in the first finite difference.
b8=F(35,1000)*F(65,1000)*a**5
r8=6*sum(comb(7,j)*min(1,max(0,1-2*(1-F(1,8)-(7-j)*a)))**2 for j in range(8))
B8=r8*(8*a-1)**7/factorial(7)/factorial(8)/b8
req(B8<F(20611,10**8),'rank-eight smooth angular upper')

# Rank 10: product lower for the seven unremoved coordinates as in the proof.
jend=[(j*a-F(85,1000))/(1+F(j,3)) for j in range(1,8)]
req(jend[0]==F(525,10000) and jend[-1]==F(3,10),'partition endpoints')
req(all(jend[i]<jend[i+1] for i in range(6)),'ordered breakpoints')
req(min((t/3)**j*a**(7-j) for j,t in enumerate(jend,1))>=F(1,10**7),'seven-coordinate product')
B10=48*2**7*(10*a-1)**9/factorial(9)/factorial(10)*10**7
req(B10<F(21488,10**8),'rank-ten smooth angular upper')

def G(h):
    p=sum((h**j/factorial(j) for j in range(12,41,2)),F(0))
    c=h*h/(43*44)
    req(c<1,'series tail')
    return p+h**42/factorial(42)/(1-c)
small=F(2**12,factorial(12))*F(1,4)**9*F(2,9)
middle=F(0)
snap=1<<36
for e in range(-2,7):
    for j in range(32):
        x=F(2)**e*(1+F(j,32));y=F(2)**e*(1+F(j+1,32))
        u=G(d['hupper'](y))*(x**-3-y**-3)/3
        middle+=F((u*snap).__ceil__(),snap)
U=F(128)
large=d['expup'](d['hupper'](U))/(2*(3-d['C4'])*U**3)
B12=d['C3']*(small+middle+large)
req(B12<F(715,10**6),'all even >=12 angular upper')
req(3*(B8+B10+B12)<F(341,10**5),'signed same-ledger smooth low <.00341')
print(f'Smooth weights: rank 8 <{float(B8):.9f}, rank 10 <{float(B10):.9f}, >=12 <{float(B12):.9f}; signed <{float(3*(B8+B10+B12)):.9f}')
