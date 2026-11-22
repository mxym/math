"""Outward rational constants for the two-order mark subtraction."""
from fractions import Fraction as Q
from math import comb
from functools import lru_cache

def require(ok,msg):
    if not ok:
        raise ArithmeticError(msg)

# Ordinary first- and second-mark derivative coefficients.
# F'(t)=sum c_j t^j on the relevant compact interval.
a=Q(1,100); b=Q(3,250); q=Q(4,3); C=Q(3446,1000)
c=(-1,-78,576,-1504,1680,-672)
def harmonic_power(j):
    return (b**j-a**j)/j
m1=-sum(c[j]*harmonic_power(j) for j in range(1,6))
m2=sum(Q(c[j],2)*sum(comb(j,h)*harmonic_power(h)*harmonic_power(j-h)
             for h in range(1,j)) for j in range(2,6))
require(Q(141,1000)<m1-m2<Q(142,1000),"signed ordinary coefficient")

prec=10**10
@lru_cache(None)
def upow(x,e):
    e=Q(e); target=x**e.numerator; d=e.denominator
    U=1
    while Q(U,prec)**d<target: U*=2
    l=0
    while U-l>1:
        n=(U+l)//2
        if Q(n,prec)**d<target:l=n
        else:U=n
    return Q(U,prec)
def lpow(x,e):
    return upow(x,e)-Q(1,prec)
def loghi(s):
    z=(s-1)/(s+1)
    n=8
    return 2*sum(z**(2*j+1)/(2*j+1) for j in range(n))+2*z**(2*n+1)/((2*n+1)*(1-z*z))
pi_lo=Q(314159,100000);pi_hi=Q(314160,100000)
from math import factorial as fac
def norm_g(j,n):
    A=Q(3,4); u,v=Q(1),j+A
    for _ in range(n):u,v=v-A*u,-A*v
    return (Q(fac(j),fac(j-n))**2/(2*(j-n)+1) + u*u/(2*A) +
             2*u*v/(2*A)**2+2*v*v/(2*A)**3)
def JJ(j,R):
    return upow(2*pi_hi,Q(1,2))*(
        upow(norm_g(j,0),Q(1,2))*
        upow(2*(upow(Q(33,1000),2*q+1)+upow(R,2*q+1)/(2*q+1)),Q(1,2))
        +upow(norm_g(j,2),Q(1,2))*
        upow(2*upow(R,2*q-3)/(3-2*q),Q(1,2)))
require(JJ(4,Q(69,100))<50 and JJ(6,Q(78,100))<83,"updated seam norm to .033")
D=10*C/(2*pi_lo)
cost1=D/(1-b)*(44*50*(upow(b,4-q)-lpow(a,4-q))/(4-q)
              +112*83*(upow(b,6-q)-lpow(a,6-q))/(6-q))
step=Q(1,8000)
grid=[a+i*step for i in range(17)]
require(grid[-1]==b,"dyadic tag mesh")
h=[loghi(t/s) for s,t in zip(grid,grid[1:])]
@lru_cache(None)
def E(t):
    return 44*50*upow(t,4-q)+112*83*upow(t,6-q)
cost2=D/(2*(1-2*b))*sum(h[i]*h[j]*(E(t+s)+E(t)+E(s))
                        for i,t in enumerate(grid[1:]) for j,s in enumerate(grid[1:]))
# The exponential tails in endpoint derivatives are <1e-5 per profile
# and all total tag harmonic masses here are less than 1.
require(cost1+Q(1,10**5)<Q(14,1000),"one-tag true prime model error")
require(cost2+Q(3,10**5)<Q(11,1000),"two-tag true prime model error")

r=Q(1251,10000); T=Q(499,1000)
def G4(s0,s1):
    # For two true least tags s=u+v, the remaining product V is
    # in [(s/2)(1-3s/2), .4(.6-s)] on every negative rank-four row.
    C=1680*(r*r+(s1-r)**2+(1-s0)**2)-528
    lo=s0/2*(1-Q(3,2)*s1)
    hi=Q(2,5)*(Q(3,5)-s0)
    if C<=0 or lo>hi:
        return Q(0)
    V=min(hi,max(lo,C/6720))
    return max(0,V*(C-3360*V))

def receiver(j,c):
    step=Q(1,10000)
    x=2*r
    tot=0
    while x<c:
        y=min(c,x+step)
        if j==4:
            B=G4(x,y)
            w=1
        elif j==5:
            maxq=(y-r)**2+(1-x-2*r)**2+3*r*r
            q1=upow(maxq,Q(1,2))
            B=(10080*q1-1056/q1)*((1-x)/3)**3
            w=c-x
        elif j==6:
            B=40320*((1-x)/4)**4
            w=c-x
        else:
            B=2112*((1-x)/5)**2+80640*7*((1-x)/5)**5
            w=c-x
        tot+=(y-x)*B*(y/2-r)*w/(T-y)
        x=y
    denom=1 if j==4 else comb(j,2)*c-(j-1)
    return 2*tot/denom

require(Q(801,2000)**2+(1-Q(801,2000)-2*r)**2+2*r*r<Q(11,35),
        "negative rank four forces owned giant mark over .4005")
U=[receiver(j,c) for j,c in [(4,Q(2,5)),(5,Q(461,1000)),
                             (6,Q(375,1000)),(7,Q(303,1000))]]
require(sum(U)<Q(852,1000),"true explicit rough receiver")
require((T-2*r)/2<r,"whole linear sieve range")
ms=[Q(9647,10**6), Q(16774,10**6), Q(451,10**6), Q(1671,10**9)]
rough=2*sum(ms)+sum(min(m*v,n*u) for m,u in zip(ms,U) for n,v in zip(ms,U))
require(rough<Q(71,1000),"actual repriced rough-only debit")

def expected_inv(j,m,B=12,P=10**8):
    from itertools import product
    num=0
    D=B**m
    increments=[(i+1)**j-i**j for i in range(B)]
    for ind in product(range(B),repeat=m):
        w,z,den=1,1,D
        for l,i in enumerate(ind,1):
            w*=increments[i]
            z*=i
            den+=z*B**(m-l)
        num+=w*((P*D**j+den**j-1)//den**j)
    return Q(num,P*B**(j*m))
# Half of the product of the two angular square-root integrals.
Droot=2*(upow(b,Q(1,2))-lpow(a,Q(1,2)))**2
doublepos=Droot*(1056*16*expected_inv(3,4)/(2*3**4*(1-Q(2,3)**2))+
                 80640*4*expected_inv(5,2)/(fac(4)*5**2*(1-Q(2,5)**2)))
singlepos=(b-a)*100*(Q(1817,100000)+Q(2177,100000)+Q(4576,100000))
massminus=m1+singlepos+doublepos
require(massminus<Q(167,1000),"ordinary A-negative mass")
cross=Q(852,1000)*Q(167,1000)
require(cross<Q(143,1000),"actual compensated rough-mark overlap")
retained=1-Q(71,1000)-2*Q(143,1000)-2*Q(25,1000)-Q(142,1000)**2
require(retained>Q(572,1000),"same-score double compensation budget")
print("narrow actual signed coefficients:",float(m1),float(m2))
print("prime seam upper before endpoint correction:",float(cost1),float(cost2))
print("actual U_4,U_5,U_6,U_7:",*[float(x) for x in U],"sum",float(sum(U)))
print("rough correction debit:",float(rough))
print("ordinary negative mass bound:",float(massminus),"double positive",float(doublepos))
print("joint budget:",float(retained))
