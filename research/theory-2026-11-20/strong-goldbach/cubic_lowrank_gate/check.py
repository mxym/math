"""Rational arithmetic for local constants; external analytic enclosures credited in Proof.md."""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement

def require(ok,msg):
    if not ok: raise ArithmeticError(msg)

def atanh_bounds(x,n):
    lo=sum(2*x**(2*j+1)/(2*j+1) for j in range(n))
    return lo,lo+2*x**(2*n+1)/((2*n+1)*(1-x*x))
def atan_bounds(x,n):
    S=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(n))
    T=S+(-1)**n*x**(2*n+1)/(2*n+1)
    return min(S,T),max(S,T)

C=F(200,53)
ll,lu=atanh_bounds(F(1,3),20)
require(6-C*F(".0155")>F("5.9415") and 6+C*F(".04825")<F("6.183"),'pointwise bounds')
require((6-C)*(5-6*lu)-C*F(".04825")>F("1.69"),'nongiant')
l75,_=atanh_bounds(F(1,6),10) # log(7/5)
require(F(".037481")<F("4.8")*(l75-F(".1408"))*F(".0405"),'rank 6 normalization')
# High-precision zeta(3) would add nothing; integral test is sufficient.
n=400
zl=sum(F(1,k**3) for k in range(1,n+1))+F(1,2*(n+1)**2)
zu=sum(F(1,k**3) for k in range(1,n+1))+F(1,2*n**2)
a,b=atan_bounds(F(1,5),15); u,v=atan_bounds(F(1,239),5)
pl,pu=16*a-4*v,16*b-4*u
require(6-pu**2/3>0,'positive log coefficient')
hmin=3+F(3,2)*zl+(6-pu**2/3)*ll-pu**2/6
hmax=3+F(3,2)*zu+(6-pl**2/3)*lu-pl**2/6
require(F("5.03667")<hmin<=hmax<F("5.03668"),'dyadic reference')
count=0
for k in range(2,7):
    for a in combinations_with_replacement(range(1,9),k):
        D=sum(a)
        A=sum((-1)**i*max(0,D-2*sum(t))**3 for i in range(k+1) for t in combinations(a,i))
        if k<=4:require(A>=0,(a,A))
        if k==3: require(A==24*a[0]*a[1]*a[2],(a,A))
        if k==5: require(A==0,(a,A))
        if k==6: require(A<=0,(a,A))
        count+=1
print(f'checked {count} exact profiles, normalized constants, and 5.03667 < reference < 5.03668')
