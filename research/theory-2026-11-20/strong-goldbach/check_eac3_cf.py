from fractions import Fraction as F
from itertools import permutations
from time import time
P=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53);D=10**50;C=10**65
def lnrat(x,J=160):
 y=F(x-1,x+1); z=y;lo=F(0)
 for j in range(J):
  lo+=2*z/(2*j+1);z*=y*y
 return lo,lo+2*z/((2*J+1)*(1-y*y))
ln2=lnrat(F(2));logs={}
for p in P:
 s=p.bit_length()-1;v=lnrat(F(p,2**s))
 logs[p]=tuple(s*t+w for t,w in zip(ln2,v))
worst=0
for p,q in permutations(P,2):
 l,u=logs[p];lq,uq=logs[q];l,u=l/uq,u/lq
 z=((l+u)/2).limit_denominator(C);A=z.numerator;H=z.denominator
 if not (D<H<=C and max(abs(H*l-A),abs(H*u-A))*2*D<1):raise ArithmeticError((p,q))
 worst=max(worst,H)
print('all 210 exact intervals and rational CF witnesses; max H=',worst)
