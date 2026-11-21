"""Independent rational checks of cubic responses, overlap and exponent arithmetic."""
from fractions import Fraction as F
from itertools import product

def ck(x):
    if not x: raise ArithmeticError('cubic reserve check failed')
def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def response(s,u):
    p=[1-2*u,-2*s]
    a=mul(mul(p,p),p)
    # Integral v^k dnu / e^gamma = -k E[v^(k-1)] for k>=1, zero at k=0.
    return -(a[1]+2*a[2]+F(9,2)*a[3])/s
for s,u,t in product([F(1,100),F(1,10000)], [F(0),F(13,72)], [F(11,124),F(3,500)]):
    ck(response(s,u)==6*(1-2*u)**2-24*s*(1-2*u)+36*s*s)
    ck(response(s,u)-response(s,u+t)==24*t*(1-2*u-2*s)-24*t*t)
# Algebra for Poisson shift in bins [a d,b d]; independent exact formulas.
for d in [F(1,100),F(1,50000)]:
    a,b=3,9
    s=2*d; lam=(b-a)*d; mu2=(b*b-a*a)*d*d/2
    c=response(s,F(0))
    no=c-24*(1-2*s)*lam+24*(lam*lam+mu2)
    plus=c-no
    single=24*(1-2*lam-2*s)*lam-24*mu2
    ck(plus-single==24*lam*lam)
    union=2*(c-1)*plus-plus**2
    onlyone=2*((c-1)*single-single*plus)
    ck(union-onlyone==2*(c-1)*(plus-single)+2*single*plus-plus**2)
ck((33*F(501,1000)-17)/20 < -F(22,1000))
ck((15*F(501,1000)-8)/8 < -F(22,1000))
ck(F(7,1000)>F(2,10000))
ck(2*(6-1)*24==240)
print('cubic integral, finite difference, Poisson shift, signed union, CRT margins: PASS')
