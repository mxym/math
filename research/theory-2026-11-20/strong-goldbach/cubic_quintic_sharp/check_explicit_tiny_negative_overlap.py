from fractions import Fraction as Q
from math import isqrt

def ck(x, label):
    if not x: raise ValueError(label)

def loghi(x):
    z=(x-1)/(x+1)
    return 2*sum(z**(2*i+1)/(2*i+1) for i in range(10))+2*z**21/(21*(1-z*z))

def root_hi(x):
    u=10**12
    return Q(isqrt(x.numerator*u*u//x.denominator)+1,u)

a=Q('.105'); b=Q(1,5000)
val=2+sum(Q(2,1000)*loghi(Q(j+1,1000)-2)/(Q(j,1000)-1)
          for j in range(3000,5000))
ck(val/5<Q('.565'), 'F1(5)')
ck((Q('.499')-Q(11,2)*b)/b>5, 'real certificate sifting ratio')
g=Q('.678')/b
triples=[(Q('1.7902'),Q('.077983212')),
    (Q(40,9)*Q('.915'),Q('.00672821')),
    (Q(2,3)/a*Q('1.2'),Q('.000001073'))]
m=Q('.08472')
ck(triples[0][1]+triples[1][1]<m,'total A mass')
v=Q('.0033960')*sum(root_hi(g*u*M) for u,M in triples)
D=2*((Q('.0111568')+Q('.0063885'))*m+v)
ck(D<Q('.218'),'overlap bound')
print("overlap upper", float(D), "remaining coefficient",float(Q('.804')-Q('.456')-D))
