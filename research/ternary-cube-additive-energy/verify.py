"""Fail-closed linear algebra-free certificates. Only integers and Fraction; no float tests."""
from fractions import Fraction as F
from math import comb
from itertools import product
from functools import lru_cache

def ck(x,msg):
    if not x: raise ArithmeticError(msg)

def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(c,a):return (c*a[0],c*a[1]) if c>=0 else (c*a[1],c*a[0])
def log12(t):
    ck(1<=t<=2,'range')
    y=(t-1)/(t+1); n=40; y2=y*y
    term=y;v=F(0)
    for j in range(n):
        v+=2*term/(2*j+1);term*=y2
    return v,v+2*term/((2*n+1)*(1-y2))
@lru_cache(maxsize=None)
def log(t):
    t=F(t); k=0
    ck(t>0,'positive logarithm')
    while t>2:t/=2;k+=1
    while t<1:t*=2;k-=1
    return add(log12(t),mul(k,log12(F(2))))

def logh(q,z):
    return add(log(3*(1+z)/(1+6*z)),mul(1-q/2,log(z)))
def P(z):return 1+12*z+6*z*z
def qlogM(q,L,U):
    return add(mul(4,(log(1+6*L)[0],log(1+6*U)[1])),mul(q-4,(log(P(L))[0],log(P(U))[1])))
def out(m,b):
    ck(b[0]>0 if m>0 else b[1]<0,'sign not certified')
    S=10**25
    return b[0].numerator*S//b[0].denominator,-((-b[1].numerator*S)//b[1].denominator)

def verify():
    # Quartic energy of a,b,c over Z, exponents per letter.
    counts={}
    for a,b,c,d in product(range(3),repeat=4):
        if a+b!=c+d:continue
        k=tuple((a,b,c,d).count(i) for i in range(3))
        counts[k]=counts.get(k,0)+1
    ck(counts=={(4,0,0):1,(0,4,0):1,(0,0,4):1,(2,2,0):4,(0,2,2):4,(2,0,2):4,(1,2,1):4},'quartic')
    coeff={0:1,7:4,21:1,3:-3,10:-1,17:-2}
    trans=[sum(c*comb(21-i,j-i) for i,c in coeff.items() if i<=j) for j in range(22)]
    ck(all(v>0 for v in trans[:-1]) and trans[-1]==0,'polynomial')
    print('Balanced-endpoint sign certificate, ascending coefficients:',trans)
    ql=F('1.4702039297178894'); qu=F('1.4702039297178896')
    ck(out(1,logh(ql,F(1,4))),'h at 1/4')
    for q,z0,sign in [(ql,'0.32606289730212337828',-1),(qu,'0.32606289730212362033',1)]:
        L=F(z0);U=L+F(1,10**20)
        ck(F(1,4)<L<U<1,'locate right branch')
        a=out(1,logh(q,L));b=out(-1,logh(q,U));c=out(sign,qlogM(q,L,U))
        print('q=',q,' z left=',z0,' width=1e-20')
        print('  enclosures in units 1e-25, log h(L), log h(U), q log M:',a,b,c)
    l=F('2.7207109973971711');u=F('2.7207109973971716')
    ck(l<4/qu<4/ql<u,'t enclosure')
    print('Certified 2.7207109973971711 < t < 2.7207109973971716')
if __name__=='__main__':verify()
