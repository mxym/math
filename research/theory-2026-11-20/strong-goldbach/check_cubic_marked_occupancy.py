#!/usr/bin/env python3
from fractions import Fraction as F
import random

def require(b,msg):
    if not b:
        raise ArithmeticError(msg)

def logpos(y,n=60):
    z=(y-1)/(y+1)
    require(0<z<1,'log range')
    s=sum((2*z**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    return s,s+2*z**(2*n+1)/((2*n+1)*(1-z*z))

D,u,w=F(399,1000),F(105,1000),F(33,100)
eta=4-F(951,1000)/w
require(D/u==F(19,5) and eta>0 and 0<(D-w)/u<(D-u)/u<3,'true sieve ranges')
A0,A1=logpos(D/u-1)
C0,C1=logpos(w/u)
H0,H1=logpos((D-u)/(D-w))
require(1/D-1/w<0,'coefficient sign')
Blo=A0/D-(C1/D+(1/D-1/w)*H0)/eta
Bhi=A1/D-(C0/D+(1/D-1/w)*H1)/eta
require(F(69312,100000)<Blo<=Bhi<F(69313,100000),'Richert bracket interval')
L2,_=logpos(F(2))
L7_5,_=logpos(F(7,5))
Jlo=L7_5-F(1408,10000)
require(F(18,1000)*2*Blo*L2*Jlo>F(33,10000),'strict fixed-target .0033')
a,b=F(49,1000),F(104,1000)
require(1-(1-2*a)**3>F(18,1000),'rank2')
require(24*a*b*F(449,1000)>F(18,1000),'rank3')
require(1-2*F(101,1000)-2*b>0,'rank4 derivative')
require(48*a*b*b*(1-a-2*b)>F(18,1000),'rank4')
r=random.Random(196)
for k in (4,6):
    for _ in range(220):
        z=[r.randint(1,1000) for _ in range(k)]
        a=[F(p,sum(z)) for p in z]
        sums=[(F(0),1)]
        for t in a:
            sums+=[(s+t,-m) for s,m in sums]
        C=sum(m*(1-2*s)**3 for s,m in sums if s<F(1,2))
        require((C>=0 if k==4 else C<=0),('cubic sign',k,a))
print('440 exact cubic signs; Richert bracket and .0033 strict rational certificate')
