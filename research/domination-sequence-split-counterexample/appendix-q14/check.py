from fractions import Fraction as F
from math import isqrt, floor, ceil
from functools import reduce
from operator import mul

def check(test,desc):
    if not test: raise ArithmeticError(desc)
q=16384;b=q*q;r=b//16;N=14*b+6*b*q
delta=F(1,64)
print('q,b,N,r=',q,b,N,r)
check(N==26_392_037_163_008 and b==268435456 and r==16_777_216,'count')
P=lambda ks:reduce(mul,(1-F(1,1<<(k+1)) for k in ks),1)
a=P((1,6));c=P((2,2,3));check(a==F(381,512) and c==F(735,1024),'products')
print('maximum one-position factors',a,c,'; 4*rho^5=',4*max(a,c)**5)
check(4*max(a,c)**5<1,'per-position exponent')
# q/5 need not be an integer: x=7b*2^(-q/5) < 2^-12 iff (7b*2^12)^5<2^q.
check((7*b*(1<<12))**5 < 1<<q,'small range')
check((65**64)<4*(64**64) and 448<512 and 7*F(1,448)==F(1,64),'tilted sum')
check(F(1,5)-F(11,64)==F(9,320),'middle exponent')
check(isqrt(q)**2==q and 1/(delta*isqrt(q))==F(1,2) and delta**2*q/2==2,'mixing')
check(8*63**2 > 128**2,'phase comparison')
check(F(9*b,320)>12 and b//2>12,'tail size')
R=2*(F(1,4095)+F(1,4096))+F(1,4096)
check(R<F(1,100),'all mixed')
print('mixed/w <',R)
check(54+F(3*q,2)<=2*q and F(2*b*q,r*r)==F(1,32),'Chebyshev')
centers=[F(N,2)+b*t for t in (F(23,42),F(5,7),F(37,42))]
# midpoint uses (23+37)/84=5/7.
w=[(ceil(t-r),floor(t+r)) for t in centers]
print('three inclusively rounded windows:',w)
check(0<=w[0][0] and w[-1][1]<=N and all(w[i][1]<w[i+1][0] for i in range(2)),'window order')
check(all(2*r-1<=end-start+1<=2*r+1 for start,end in w),'counts')
L=F(31,32)/(2*r+1);H=(F(1,16)+F(1,100))/(2*r-1)
check(L>H,'strict valley');print('outer/w >=',L,'middle/w <=',H,'ratio L/H=',L/H)
