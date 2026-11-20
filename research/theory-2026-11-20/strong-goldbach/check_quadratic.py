"""Certified one-dimensional reference-envelope bounds. Standard library, exact rationals."""
from fractions import Fraction as F
from math import factorial

def require(condition, detail=None):
    if not condition:
        raise RuntimeError(detail or "A rational envelope check failed")
def ceil(x): return -(-x.numerator//x.denominator)
def floor(x):return x.numerator//x.denominator
def up(x,scale=10**10): return F(ceil(x*scale),scale)
def dn(x,scale=10**10): return F(floor(x*scale),scale)
def atanh_log(x):
    # x in [1,2], log x = 2 atanh((x-1)/(x+1)).
    r=(x-1)/(x+1); v=r; s=F(0); n=10
    for j in range(n):
        s+=v/(2*j+1);v*=r*r
    return (dn(2*s),up(2*(s+v/((2*n+1)*(1-r*r)))))
l2,u2=atanh_log(F(2))
def logup(x):
    require(x>=1)
    e=x.numerator.bit_length()-x.denominator.bit_length()
    if F(2)**e>x:e-=1
    m=x/F(2)**e
    require(1<=m<2 and e>=0)
    return e*u2+atanh_log(m)[1]
def atan_range(u,n):
    p=u;s=F(0)
    for j in range(n):
        s+=p/(2*j+1);p*=-u*u
    p/=2*n+1
    return dn(min(s,s+p)),up(max(s,s+p))
al,au=atan_range(F(1,5),12);bl,bu=atan_range(F(1,239),6)
pl,pu=16*al-4*bu,16*au-4*bl
require(F(314159,100000)<pl<pu<F(314160,100000))
def atanup(x):
    if x<=1:return atan_range(x,12)[1]
    return pu/2-atan_range(1/x,12)[0]
C=4/pl*(sum((logup(F(n))/(4*n*n-1) for n in range(2,11)),F(0))+(logup(F(10))+1)/(10*(4-F(1,11**2))))
require(C<F(31,100))
def R7(x):
    z=up(x,10**7); D=10**12
    a=ceil(D*z**7/factorial(7)); total=a
    for k in range(7,69,2):
        a=ceil(a*z*z/((k+1)*(k+2)))
        total+=a
    require(z*z/(70*71)<F(1,2))
    return F(total+a,D)  # geometric bound for the rest after term 69.
def grid():
    M=64
    for j in range(-1,18):
        for i in range(M):
            yield (F(2)**j*F(M+i,M),F(2)**j*F(M+i+1,M))
A=B=F(0)
for t,u in grid():
    area=(1/t**2-1/u**2)/2
    z=min(u, 2*logup(1+u*u)/pl+2*C)
    A+=up(2/pl*area*R7(z),10**13)
    z=min(u,2*atanup(u/2))
    # upper bound on the positive alternating signed tail by first omitted term
    B+=up(2/pl*area*z**7/factorial(7),10**13)
A+=F(1,100000)+F(1,4096)
B+=F(1,100000)+F(8,2**36)
require(A<F(6148,100000) and B<F(418,100000),(float(A),float(B)))
Q3L=l2-pu**2/24;Q3U=u2-pl**2/24
require(F(2819,10000)<Q3L<Q3U<F(2820,10000))
print('Upper raw absolute tail',float(A),'upper signed tail',float(B))
print('Actual higher positive coefficient <',float(2*(A+B)))
print('Combined two/three model',float(Q3U+F(1,2)))
