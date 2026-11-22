"""Outward rational constants for the two-order mark subtraction."""
from fractions import Fraction as Q
from math import comb
from functools import lru_cache

def require(ok,msg):
    if not ok:
        raise ArithmeticError(msg)

# Ordinary first- and second-mark derivative coefficients.
# F'(t)=sum c_j t^j on the relevant compact interval.
a=Q(1,100); b=Q(2,125); q=Q(4,3); C=Q(3446,1000)
c=(-1,-78,576,-1504,1680,-672)
def harmonic_power(j):
    return (b**j-a**j)/j
m1=-sum(c[j]*harmonic_power(j) for j in range(1,6))
m2=sum(Q(c[j],2)*sum(comb(j,h)*harmonic_power(h)*harmonic_power(j-h)
             for h in range(1,j)) for j in range(2,6))
require(Q(405,1000)<m1-m2<Q(406,1000),"signed ordinary coefficient")

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
grid=[a+i*step for i in range(49)]
require(grid[-1]==b,"dyadic tag mesh")
h=[loghi(t/s) for s,t in zip(grid,grid[1:])]
@lru_cache(None)
def E(t):
    return 44*50*upow(t,4-q)+112*83*upow(t,6-q)
cost2=D/(2*(1-2*b))*sum(h[i]*h[j]*(E(t+s)+E(t)+E(s))
                        for i,t in enumerate(grid[1:]) for j,s in enumerate(grid[1:]))
# The exponential tails in endpoint derivatives are <1e-5 per profile
# and all total tag harmonic masses here are less than 1.
require(cost1+Q(1,10**5)<Q(54,1000),"one-tag true prime model error")
require(cost2+Q(3,10**5)<Q(109,1000),"two-tag true prime model error")
save=1-2*Q(163,1000)-Q(406,1000)**2
require(save>Q(509,1000),"literal two-order deletion remainder")
print("true ordinary marks m1,m2:",float(m1),float(m2))
print("one-tag and two-tag seam prices before tiny correction:",float(cost1),float(cost2))
print("remaining coefficient lower:",float(save))
