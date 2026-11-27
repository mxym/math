#!/usr/bin/env python3
"""Exact small angular constants and odd transport gaps; no dependencies."""
from fractions import Fraction as F
from math import comb,isqrt
if not __debug__:raise RuntimeError('enable assertions')
def add(*a):
    q=[F(0)]*max(map(len,a))
    for z in a:
        for j,x in enumerate(z):q[j]+=x
    return q
def mul(*a):
    r=[F(1)]
    for z in a:
        b=[F(0)]*(len(r)+len(z)-1)
        for i,x in enumerate(r):
            for j,y in enumerate(z):b[i+j]+=x*y
        r=b
    return r
def c(a,z):return mul([F(a)],z)
def bern(poly,H):
    n=len(poly)-1
    return [sum(poly[i]*H**i*F(comb(k,i),comb(n,i))for i in range(k+1))for k in range(n+1)]
# Machin's identity and alternating series give strict brackets for pi.
def ataninv(q):
    a=sum(F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(12))
    return a,a+F(1,25*q**25)
a,b=ataninv(5);u,v=ataninv(239)
assert 16*a-4*v>F(3141592653589793,10**15) and 16*b-4*u<F(3141592653589794,10**15)
pl,pu=F(3141592653589793,10**15),F(3141592653589794,10**15)
from math import factorial
def trig(q,n):
    # argument q*pi lies in [0,pi/2]; cosine decreases, sine increases
    a,b=q*pl,q*pu
    assert 0<=q<=F(1,2)
    def approx(x,m):return sum(F((-1)**j,factorial(n+2*j))*x**(n+2*j) for j in range(m))
    return (approx(b if n==0 else a,8),approx(a if n==0 else b,9))
def cos(a,k,side):return trig(F(a,k),0)[side]
def tanhi(a,k):return trig(F(a,k),1)[1]/cos(a,k,0)
assert pu/9<F(35,100) and tanhi(2,9)<F(85,100) and tanhi(1,9)<F(37,100)
assert F(7)/(cos(2,7,0)*cos(1,7,0))<F(1248,100)<F(9)/(cos(2,9,1)*cos(1,9,1))
assert cos(2,5,1)<F(1,2)<cos(2,7,0)
def L7lo(s):
    c,d=cos(1,7,1),cos(3,7,1)
    return 14*(1-((1+s)/2+c*d)/(cos(1,7,0)+cos(3,7,0)))
assert L7lo(cos(2,5,1))>3 and L7lo(F(1,2))>F(215,100)
T=[ [1],[0,1] ]
for j in range(2,7):T.append(add(mul([0,2],T[-1]),c(-1,T[-2])))
assert add(c(3,T[3]),c(-2,T[2]),c(-1,T[6]))==mul([1,-1],[-3,0,4],[-1,2,8,8])
assert add([-1],c(3,T[3]),c(-2,T[4]))==mul([1,-1],[1,4],[-3,0,4])
A5=10*(1-cos(1,5,1))
for N,H in [(74,512),(76,681),(128,306),(130,420),(132,500)]:
    assert 4*N*F(H,10000)**2<2*A5
print('all fixed trigonometric inequalities and factorizations: PASS')
rows=[(6,73,1150,221,1945),(6,75,3000,182,2150),
      (7,127,665,221,1931),(7,129,1940,183,2093),(7,131,2300,147,2150)]
for d,N,H0,b0,out in rows:
    P={6:36,7:63}[d];p=(N-5)//2;K=isqrt(p-1)+1;H=F(H0,100000);b=F(b0,100)
    assert F(1,16)>=F(9,4)*(K+F(1,2))*H**2+F(5,4)*(K+1)**2*H**3
    E=[0,0,p];EE=mul(E,E)
    lo=add(c(p,mul([1,0,-1],[1,0,-1])),[b])
    lo=c(F(3,4*P),mul(lo,lo))
    diag=c(F(3,4),add([p],c(-4,E),c(6,EE)))
    pair=add(c(F(3,16),add(c(p,E),EE)),
             mul(add([1],c(F(1,2),E)),add([1+F(K,2)],c(F(3,8),E)),EE))
    mixed=c(2*b,[0,F(p,8),F(21*p,16),F(9*p,4),F(5*p,4)])
    difference=add(lo,c(-1,diag),c(-1,pair),c(-1,mixed),[-(F(13,50)+F(101,1800))*b*b])
    bs=bern(difference,H)
    assert min(bs)>0,(d,N,bs)
    assert A5+8*p*H**2>F(out,1000)
    print(d,N,'cost >',F(out,1000),'Bernstein gap >',int(min(bs)*10**7),'e-7')
