"""Directed rational constants and literal CRT/finite-sign regression. No sieving theorem is numerically inferred."""
from fractions import Fraction as F
from math import gcd
from itertools import combinations
def check(ok,label):
    if not ok: raise ArithmeticError(label)
def atan(x,n):
    a=sum((-1)**i*x**(2*i+1)/(2*i+1) for i in range(n))
    b=a+(-1)**n*x**(2*n+1)/(2*n+1)
    return min(a,b),max(a,b)
a,b=atan(F(1,5),18); c,d=atan(F(1,239),7)
pi0,pi1=16*a-4*d,16*b-4*c
x=F(1,3); n=23
ell0=sum(2*x**(2*i+1)/(2*i+1) for i in range(n))
ell1=ell0+2*x**(2*n+1)/((2*n+1)*(1-x*x))
n=16000; den=10**22
partial=F(sum(den//(i**3) for i in range(1,n+1)),den)
z0,z1=partial+F(1,2*(n+1)**2),partial+F(n,den)+F(1,2*n**2)
m0=3+3*z0/2+(6-pi1*pi1/3)*ell0-pi1*pi1/6
m1=3+3*z1/2+(6-pi0*pi0/3)*ell1-pi0*pi0/6
check(F('5.03667154996')<m0<=m1<F('5.03667154998'),'M')
check(F('6.07334309992')<2*(m0-2)<=2*(m1-2)<F('6.07334309996'),'parity endpoint')
good=F('5.9415')
rho0,rho1=(good-m1)/(m1-4),(good-m0)/(m0-4)
check(F('.8728207599')<rho0<=rho1<F('.8728207600'),'sharp parity threshold')
check(F('4.8585027245')<m1/(m1-4)<=m0/(m0-4)<F('4.8585027246'),'balanced drift')
# In each actual (q,a,k) CRT cell, y/g is a unit modulo qk/g,
# also when the gcd shares primes with the residual modulus.
labels=[1,2,3,5,7,6,10,14,15,21]; count=0; repeated=0
for P in range(16,70,2):
    for q in range(1,19):
        for a in range(1,q+1):
            if gcd(q,a)>1:continue
            for k in labels:
                if gcd(k,q)>1:continue
                D=q*k; y=next(y for y in range(D) if (P-y)%q==a%q and (P-y)%k==0)
                g=gcd(y,D); h=D//g
                check(g==gcd(P-a,q)*gcd(P,k) and gcd(y//g,h)==1,'reduced residual')
                check(all((v%q==(P-a)%q and v%k==P%k)==(v%g==0 and (v//g)%h==(y//g)%h) for v in (y,y+1,y+D,y+2*D,y+g)), 'cell equivalence')
                count+=1; repeated+=int(gcd(g,h)>1)
check(repeated>0,'required cases with gcd(g,h)>1')
print('checked',count,'CRT cells including',repeated,'overlapping gcd/residuals; certified 6.0733430999 < synthetic endpoint < 6.0733431000 and .8728207599 < parity threshold < .8728207600')
