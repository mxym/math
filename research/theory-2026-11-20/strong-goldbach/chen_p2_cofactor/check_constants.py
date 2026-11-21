"""Directed interval certificate using rational arithmetic only, also under -O."""
from fractions import Fraction as F

def ck(x, label):
    if not x: raise ArithmeticError(label)
D=10**12
def down(x): return F((x*D).__floor__(),D)
def up(x): return F((x*D).__ceil__(),D)
def log_bounds(x):
    ck(x>=1,"log argument")
    z=(x-1)/(x+1); n=11
    z2=z*z; term=z; val=0
    for j in range(n):
        val+=2*term/(2*j+1); term*=z2
    return down(val),up(val+2*term/((2*n+1)*(1-z2)))
def upper_integral(a,b,major,n=1024):
    step=(b-a)/n
    return step*sum(up(major(a+step*i,a+step*(i+1))) for i in range(n))
th=F(479,1000); s=10*th; eta=F(1,25)
ck(eta+(1-eta)*th<F(1,2),"BV level")
ck(F(499,1000)/F(249,1000)<3,"switched linear sieve")
C=log_bounds((s-1)*(3*th-1))[0]/th
J=upper_integral(F(2),s-2,lambda a,b:
    log_bounds(b-1)[1]/a*log_bounds((a+1)*(s-a-1)/(s-1))[1])/th
I=upper_integral(F(1,10),F(1,3),lambda a,b:
    log_bounds(2-3*a)[1]/(a*(1-a)))/F(499,1000)
lower=down(C-J-I)
print("direct lower",float(C),"direct integral loss upper",float(J),
      "switched cost upper",float(I),"net exact lower",lower)
ck(lower>F(3,100),"positive Chen margin not certified")
