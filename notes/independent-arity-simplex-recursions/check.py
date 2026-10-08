#!/usr/bin/env python3
"""Independent-arity simplex recursion: exact rational proof certificate.

Only integer/Fraction arithmetic occurs in mathematical comparisons.
The argument reducing infinite parameter ranges is in PROOF.md.
No `assert` statements occur in the certificate.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial

L = F(131, 125)
LOG_TERMS = 18
ATAN_TERMS = 16

def need(cond, label):
    if not cond:
        raise RuntimeError("certificate failed: " + label)

def arctan_interval(x, count=ATAN_TERMS):
    x = F(x)
    need(0 < x < 1, "arctan range")
    s = F(0)
    for n in range(count):
        s += (-1)**n * x**(2*n+1) / (2*n+1)
    err = x**(2*count+1)/F(2*count+1)
    return (s, s+err) if count % 2 == 0 else (s-err, s)

a5lo,a5hi = arctan_interval(F(1,5))
a239lo,a239hi = arctan_interval(F(1,239))
PI_LO, PI_HI = 16*a5lo-4*a239hi, 16*a5hi-4*a239lo
need(F(3) < PI_LO < PI_HI < F(4), "Machin pi enclosure")

def unit_log_interval(y):
    need(1 <= y < 2, "unit logarithm range")
    if y == 1:
        return F(0),F(0)
    z = (y-1)/(y+1)
    zsq = z*z
    term = z
    s = F(0)
    for j in range(LOG_TERMS):
        s += term/F(2*j+1)
        term *= zsq
    lo=2*s
    return lo,lo+2*term/(F(2*LOG_TERMS+1)*(1-zsq))

# Treat log 2 directly using the convergent z=1/3 series:
def log_two_interval():
    z=F(1,3); zsq=z*z; term=z; s=F(0)
    for j in range(LOG_TERMS):
        s+=term/F(2*j+1)
        term*=zsq
    v=2*s
    return v,v+2*term/(F(2*LOG_TERMS+1)*(1-zsq))

LN2_LO,LN2_HI=log_two_interval()

@lru_cache(maxsize=None)
def log_interval(x):
    x=F(x)
    need(x>0,"logarithm positive")
    shift=0
    while x>=2:
        x/=2; shift+=1
    while x<1:
        x*=2; shift-=1
    lo,hi=unit_log_interval(x)
    if shift>=0:
        return lo+shift*LN2_LO,hi+shift*LN2_HI
    return lo+shift*LN2_HI,hi+shift*LN2_LO

def lnlo(x):
    return log_interval(F(x))[0]

def lnhi(x):
    return log_interval(F(x))[1]

L2PI_LO = lnlo(2*PI_LO)
L2PI_HI = lnhi(2*PI_HI)

@lru_cache(maxsize=None)
def logg_interval(n):
    need(isinstance(n,int) and n>=1,"g integer")
    if n<=20:
        return log_interval(F(n**n,factorial(n)))
    # Direct Robbins two-sided factorial bound for every n >= 21.
    base_lo=F(n)-(L2PI_HI+lnhi(n))/2-F(1,12*n)
    base_hi=F(n)-(L2PI_LO+lnlo(n))/2-F(1,12*n+1)
    return base_lo,base_hi

def Ahi(p):
    return lnhi(p+1)+logg_interval(p)[1]

def delta_lo(p):
    return L*p-Ahi(p)

def logC_hi(m,k,p):
    T=m*k
    c=F(k-1,T-1)
    B=F(1)+(L2PI_HI+lnhi(m)+lnhi(p+c))/2-lnlo(p+1)
    return lnhi(k)/2+(k-1)*B+F(k,12*m*p)

def q_hi(m,k):
    return F(k-1,2)*(lnhi(m)-lnlo(k))

def recursion_numerator_hi(m,k,p,levels=0):
    T=m*k; c=F(k-1,T-1)
    s=Ahi(p)
    d=p
    for j in range(levels):
        nd=T*d+k-1
        logD_hi=(lnhi(k)-
            (k-1)*(lnlo(p+1)+j*lnlo(k))+
            logg_interval(nd)[1]-k*logg_interval(m*d)[0])
        s+=logD_hi/F(T**(j+1))
        d=nd
    q=q_hi(m,k)
    s+=(logC_hi(m,k,p)+levels*q)/(F(T**levels)*(T-1))
    s+=q/(F(T**levels)*(T-1)**2)
    return s

def all_parameter_tails():
    # For p=1,...,31 prove delta_p = L*p-log R(T_p) > 3/20.
    for p in range(1,32):
        need(delta_lo(p)>F(3,20), "delta small p="+str(p))
    # Robbins gives delta_p >= phi(p) for p>=32. phi'(p)>0
    # since 6/125-1/33-12/385^2 >0 for p>=32.
    derivative_bound=F(6,125)-F(1,33)-F(12,385**2)
    phi32=F(6,125)*32-lnhi(33)+(L2PI_LO+lnlo(32))/2+F(1,385)
    need(derivative_bound>0 and phi32>F(2,3), "delta all p>=32")

    # For m>=32: c h <= (log(pi*m)/2-6/125)/m,
    # and all remaining positive terms are decreasing in m>=32.
    m=32
    mtail=(lnhi(PI_HI*m)/2-F(6,125))/m
    mtail+=F(1,4)/(F(m)-F(1,2))
    mtail+=F(1,12*m)/(F(m)-F(1,2))
    mtail+=lnhi(m)/F(2*m*(2*m-1))
    need(mtail<F(3,20), "all m>=32")
    need(lnlo(3)>1 and lnhi(3)<F(6,5), "E3 monotonicity")

    # For 2<=m<=31, p>=32, use delta>=2/3, h<=17/20.
    hbound=(lnhi(2*PI_HI*F(31,33)))/2-F(6,125)
    need(hbound<F(17,20),"p-tail h")
    err=F(17,40)+F(1,6)+F(1,1152)+F(1,25)
    need(err<F(2,3),"all p>=32")
    return mtail,hbound

def k_tails():
    K=32
    # m>=3: for k>=32>m, q<=0. Independent m,p finite
    # comparison includes all continuous k>=32 via log k/k monotonicity.
    n=0
    for m in range(2,32):
        for p in range(1,32):
            if m==2 and p<8:
                continue
            H=F(-6,125)+(L2PI_HI+lnhi(m)+lnhi(F(p)+F(1,m)))/2-lnlo(p+1)
            gain=max(F(0),H)/m
            error=(lnhi(K)/F(2*K)+F(1,12*m*p))/(F(m)-F(1,K))
            need(gain+error<delta_lo(p),
                 "k>=32 m="+str(m)+" p="+str(p))
            n+=1
    # m=2,p=1..7: restart after exact first recurrence level.
    # Drop the nonpositive q-tail; the other k-dependent contributions
    # are dominated by log K / K and k=K.
    for p in range(1,8):
        Bbar=F(1)+(L2PI_HI+lnhi(2)+lnhi(F(p)+F(1,2)))/2-lnlo(p+1)
        Bbar_lo=F(1)+(L2PI_LO+lnlo(2)+lnlo(F(p)+F(1,2)))/2-lnhi(p+1)
        C0=lnhi(p+1)-1-(L2PI_LO+lnlo(F(2*p)+F(1,2)))/2
        need(Bbar_lo>0 and C0<0, "special k-tail side signs p="+str(p))
        E0=2*p+1-lnlo(p+1)-logg_interval(2*p)[0]
        lhs=Ahi(p)+E0/2+lnhi(K)/F(4*K)
        lhs+=(Bbar+F(1,24*p)+lnhi(K)/F(2*K))/F(2*(2*K-1))
        rhs=L*(F(p)+F(K-1,2*K-1))
        need(lhs<rhs,"special k>=32 p="+str(p))
        n+=1
    return n

def finite_core():
    regular=0
    restarted=0
    for m in range(2,32):
        for k in range(2,32):
            c=F(k-1,m*k-1)
            for p in range(1,32):
                if (m,k,p)==(2,2,5):
                    continue
                levels=3 if m==2 and p<=7 else 0
                s=recursion_numerator_hi(m,k,p,levels)
                need(s<L*(F(p)+c),
                     "finite m="+str(m)+" k="+str(k)+" p="+str(p))
                if levels:
                    restarted+=1
                else:
                    regular+=1
    return regular,restarted

def main():
    mt,pt=all_parameter_tails()
    kt=k_tails()
    reg,res=finite_core()
    need((reg,res,kt)==(27690,209,930),"full loop counts")
    need(lnlo(F(14267,5000))>L,
         "lower endpoint separation from v5")
    print("PASS: independent-arity homogeneous recursion classification")
    print("finite regular exclusions:",reg)
    print("finite three-level exclusions:",res)
    print("independent k-tail certificates:",kt)
    print("analytic tails: m>=32, p>=32, k>=32")
    print("winner: (m,k,p)=(2,2,5), inherited lower witness from 005 v5")
    print("competitor upper: exp(131/125) < 14267/5000")
    print("methods: rational Machin pi, rational atanh log, factorial / Robbins bounds")
    print("no float or assertion-dependent checks")

if __name__=="__main__":
    main()
