"""Rational enclosure for the high-row constant in CenteredMarkerHighRows."""
from math import factorial
from fractions import Fraction as Q

scale = 10**13

def log_near_upper(a, b):
    if not b <= a <= 2*b:
        raise ValueError((a, b))
    t, u = a-b, a+b
    # t/u <= 1/3. Truncation at 13 terms leaves less than
    # one fixed-point unit; the floor losses cost 13 more.
    if not 2*scale*9 < 27*8*3**27:
        raise ValueError("log-tail coarsening not justified")
    return 14 + sum((2*scale*t**j)//(j*u**j) for j in range(1, 27, 2))

def log_upper(q):
    a, b = q.numerator, q.denominator
    if a < b:
        raise ValueError(q)
    e = 0
    while a >= 2*b:
        b *= 2
        e += 1
    return Q(log_near_upper(a,b)+e*log_near_upper(2,1),scale)

a=Q(31,200)
m=1024
C3 = Q(0)
for l,r,part in [(a,Q(1,4),0), (Q(1,4),Q(1,3),1)]:
    h=(r-l)/m
    for i in range(m):
        x=l+i*h
        ratio=1/(1-2*(x+h)) if part==0 else (1-2*x)/x
        bound=2*h*log_upper(ratio)/(x*(1-x))
        # Round each rational summand upward to this common grid.
        C3+=Q((bound.numerator*scale+bound.denominator-1)//bound.denominator,scale)
U5=(1-5*a)**4/(factorial(4)*factorial(5)*a**4*(1-4*a))
total=C3+18*U5
if not total<Q(983,1000):
    raise ValueError(total)
print("C3 upper:",float(C3),"U5:",float(U5),"total upper:",float(total))
