#!/usr/bin/env python3
"""Exact replay for the actual quartic half-zero compensated debit."""
from fractions import Fraction as Q
from itertools import product
from math import ceil,isqrt
def require(b):
    if not b:
        raise ValueError("exact certificate inequality failed")

sc=10**12
J=[[sc]*7001]
for j in range(2,9):
    z=[0]*7001
    for i in range(1001,7001):
        z[i]=z[i-1]+(J[-1][i-1000]+i-2)//(i-1)
    J.append(z)
D=Q(499,1000)
def ulog(x):
    t=(x-1)/(x+1)
    return 2*sum(t**(2*j+1)/(2*j+1) for j in range(7))+2*t**15/(15*(1-t*t))
def llog(x):
    t=(x-1)/(x+1)
    return 2*sum(t**(2*j+1)/(2*j+1) for j in range(7))
def rup(x, scale=10**15):return Q(ceil(x*scale),scale)
def rdown(x, scale=10**15):return Q(int(x*scale),scale)
a=Q(145,1000)
def rough():
    g=lambda s:max(Q(0),36*(1-s)**2+12*(a*a+(s-a)**2)-14)
    d=Q(1,10000)
    end=Q(428,1000)
    u3=d*sum(2*((2*a+(i+1)*d)/2-a)/(D-(2*a+(i+1)*d))*g(2*a+i*d)
             for i in range(int((end-2*a)/d)))
    m3=d*sum(((2*a+(i+1)*d)/2-a)/(1-(2*a+(i+1)*d))*g(2*a+i*d)
             for i in range(int((end-2*a)/d)))
    f=lambda u:(1-u)**3/(D-u)
    u4=Q(288,27)*d*sum(max(f(a+i*d),f(a+(i+1)*d))
                       for i in range(int((Q(1,4)-a)/d)))
    b=Q(45,100)
    k=(b-2*a)/d
    require(k.denominator==1)
    u5=2*Q(16903,16000)/(10*b-4)*d*sum(
        ulog((2*a+(i+1)*d-a)/a)/(2*a+i*d)
        *(b-(2*a+i*d))/(D-(2*a+i*d)) for i in range(int(k)))
    m4=(1-4*a)**3
    m5=Q(4940,2880)*(1-5*a)**4
    M=list(map(rup,[m3,m4,m5]))
    U=list(map(rup,[u3,u4,u5]))
    require(sum(M)<Q(90611,10**6))
    require(U[0]<Q(59,1000) and U[1]<Q(1927,1000) and U[2]<Q(354,1000))
    return M,U

def mark(i,j,second):
    p,q=Q(i+1,1000),Q(j+1,1000)
    h=p+q;c=1-h;C=c+Q(2,1000)
    D0=Q(555,1000)-h
    z=max(Q(1325,10000),D0/3,q+Q(5,10000) if second else Q(0))
    if not (2<D0/z<=3 and C/z<8 and q<z<Q(187,1000)):
        require(second)
        return None
    idx=ceil((C/z-1)*1000)
    m3upper=Q(3446,1000)*sum(Q(row[idx],sc) for row in J[3:])/c
    lower=2*llog(D0/z-1)/D0-m3upper
    if lower<=0:
        require(second)
        return None
    if second:
        v=p*p+q*q+2*z*z+(C-2*z)**2
        B=Q(isqrt((10**6*v.denominator)//v.numerator),1000)
        require(B*B*v<=1)
        w=min(36*c*c+12*(Q(i,1000)**2+Q(j,1000)**2)-14,
              144*z*(c-z), B*288*z*z*(c-2*z))
    else:
        require(2*Q(132,1000)**2+2*z*z+(C-2*z)**2<Q(25,49))
        w=min(36*c*c-14, 144*z*(c-z), Q(7,5)*288*z*z*(c-2*z))
    require(w>0 and 1<(D-h)/z<3)
    V=max(36*C*C+12*(p*p+q*q)-14,36*C*C,28+32*C*C)
    mass=rup(w*sum(Q(row[idx],sc) for row in J[:3])/c/10**6)
    cap=rup(w*(2/(D-h))/10**6)
    rebate=rdown(lower*w,10**9)/10**6
    return mass,cap,rebate,w/V
def bank(second):
    data=[]
    for i in range(5,132):
        for j in (range(132,187) if second else range(i+1,132)):
            r=mark(i,j,second)
            if r is not None:
                data.append(r)
    m,u,p=map(sum,zip(*(r[:3] for r in data)))
    w=min(r[3] for r in data)
    require(len(data)==(3661 if second else 8001))
    require(w>Q(93 if second else 73,1000))
    return m,u,p,w

m,u=rough()
b1=bank(False)
b2=bank(True)
require(b1[2]==Q(105769197972637,10**15))
require(b2[2]==Q(28817505038252,10**15))
print("rough source masses and receiver constants:",
      [(float(x),float(y)) for x,y in zip(m,u)])
print("old bank mass, receiver, rebate, fraction:",*[float(x) for x in b1])
print("new bank mass, receiver, rebate, fraction:",*[float(x) for x in b2])
def ledger(m,u,p):
    return 2*(sum(m)-sum(p))+sum(min(m[i]*u[j],m[j]*u[i])
           for i,j in product(range(len(m)),repeat=2))
r0=ledger(m,u,[])
print("refined rough debit:",float(r0))
for nb,cap0 in [(1,Q(527,1000)),(2,Q(693,1000))]:
    b=[b1,b2][:nb]
    ans=ledger(m+[x[0] for x in b],u+[x[1] for x in b],[x[2] for x in b])
    print(f"combined {nb}-bank debit:",float(ans))
    require(ans<cap0)
