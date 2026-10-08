#!/usr/bin/env python3
"""Exact rational certificate for all independent homogeneous product/join arities.

No floats, interval package, external solver, assert statements, or network needed.
Logarithms use a proved atanh power-series enclosure. Robbins bounds are
proved standard analytic inequalities; no finite calculation substitutes them.
"""
from functools import lru_cache
from fractions import Fraction as F
from math import factorial

TERMS = 16
PI_LO, PI_HI = F(333, 106), F(355, 113)
THRESH = F(131, 125)
RATE_LO = F(14267, 5000)
DELTA = F(6, 125)


def require(condition, msg):
    if not condition:
        raise RuntimeError(msg)


def arctan_interval(z, N=10):
    require(F(0) < z < F(1) and N % 2 == 0, 'atan input')
    sm = sum(((-1)**j)*z**(2*j+1)/F(2*j+1) for j in range(N))
    return sm, sm+z**(2*N+1)/F(2*N+1)


def check_pi():
    # Machin: pi=16 arctan(1/5)-4 arctan(1/239).
    a,b = arctan_interval(F(1,5))
    c,d = arctan_interval(F(1,239))
    require(PI_LO < 16*a-4*d and 16*b-4*c < PI_HI,
            'pi enclosure is not certified')


@lru_cache(maxsize=None)
def ln2_interval():
    z=F(1,3); power=z; acc=F(0)
    for j in range(TERMS):
        acc+=2*power/F(2*j+1)
        power*=z*z
    return acc,acc+2*power/(F(2*TERMS+1)*(1-z*z))


@lru_cache(maxsize=150000)
def log_interval(x):
    x=F(x)
    require(x>0,'log input must be positive')
    # Normalize exactly by powers of two; avoid loops proportional to bit size.
    k=x.numerator.bit_length()-x.denominator.bit_length()
    y=x/F(2**k) if k>=0 else x*F(2**(-k))
    if y<1:
        y*=2;k-=1
    elif y>=2:
        y/=2;k+=1
    require(F(1)<=y<F(2),'log normalization')
    z=(y-1)/(y+1)
    power=z;sm=F(0)
    for j in range(TERMS):
        sm+=2*power/F(2*j+1)
        power*=z*z
    err=2*power/(F(2*TERMS+1)*(1-z*z))
    lo,hi=ln2_interval()
    return (sm+k*lo,sm+err+k*hi) if k>=0 else (sm+k*hi,sm+err+k*lo)


def log_lo(x):return log_interval(F(x))[0]
def log_hi(x):return log_interval(F(x))[1]
def log_pi_lo(x):return log_lo(2*PI_LO*F(x))
def log_pi_hi(x):return log_hi(2*PI_HI*F(x))


@lru_cache(maxsize=None)
def g(n):
    require(isinstance(n,int) and n>=1,'g domain')
    return F(n**n,factorial(n))


def seed_log_hi(p):return log_hi(p+1)+log_hi(g(p))
def seed_log_lo(p):return log_lo(p+1)+log_lo(g(p))


def constants_upper(m,k,p):
    T=m*k;c=F(k-1,T-1)
    A=(F(k-1)+log_hi(k)/2+F(k-1,2)*log_hi(m)
       +F(k-1,2)*log_pi_hi(F(p)+c)
       -F(k-1)*log_lo(p+1)+F(k,12*m*p))
    b=F(k-1,2)*(log_hi(m)-log_lo(k))
    return A,b,c


def U0_hi(m,k,p):
    T=m*k;A,b,c=constants_upper(m,k,p)
    return (seed_log_hi(p)+A/F(T-1)+b/F((T-1)**2))/(F(p)+c)


def U1_hi(m,k,p):
    # Exact seed and exact g(mp), Robbins upper estimate for g(d1).
    T=m*k;A,b,c=constants_upper(m,k,p)
    d1=k*(m*p+1)-1
    logD0=(log_hi(k)-F(k-1)*log_lo(p+1)+F(k-1)
           -log_pi_lo(d1)/2-F(k)*log_lo(g(m*p)))
    # Correct linear component of log g(d1)-k log g(mp):
    # log g(d1) < d1 - 1/2 log(2 pi d1).
    logD0 += F(m*k*p)
    q1=T*seed_log_hi(p)+logD0
    return (q1 + A/F(T-1)+b*(F(1,T-1)+F(1,(T-1)**2)))/(F(d1)+c)


def U_refined_hi(m,k,p,J):
    # Robbins 1/(12n+1) term, rigorous finite-level upper bound.
    T=m*k;A,b,c=constants_upper(m,k,p)
    d=p;q=seed_log_hi(p)
    for j in range(J):
        dn=T*d+k-1
        ld=(log_hi(k)-F(k-1)*log_lo(p+1)
            -F(j*(k-1))*log_lo(k)+F(k-1)
            +F(k,2)*log_pi_hi(m*d)
            -log_pi_lo(dn)/2
            +F(k,12*m*d)-F(1,12*dn+1))
        q=T*q+ld
        d=dn
    return (q+A/F(T-1)+b*(F(J,T-1)+F(1,(T-1)**2)))/(F(d)+c)


def F_tail_hi(p):
    return (log_hi(p+1)-log_pi_lo(p)/2+F(33,28*(p+1))
            +F(1,8)+F(1,20)+F(1,36*p))


def F_tail_derivative(p):
    return (F(1,p+1)-F(1,2*p)-F(33,28*(p+1)**2)
            -F(1,36*p*p))


def m_large_hi(p):
    return (log_hi(p+1)-log_pi_lo(p)/2
            +log_pi_hi(F(20,p+1))/40
            +F(1,78)+F(1,156)+F(1,4680*p))


def k_large_hi(m,p):
    c_lo=F(19,20*m-1);c_hi=F(1,m)
    # J exact-seed bound; c log(t(c)) bounded by a true endpoint maximum.
    ell_hi=log_pi_hi(F(m)*(F(p)+c_hi)/F((p+1)**2))
    # Only upper ell is needed, and multiplication by either endpoint of c.
    ell=ell_hi
    return (seed_log_hi(p)-F(p)+max(c_lo*ell,c_hi*ell)/2
            +log_hi(20)/F(2*(20*m-1))
            +F(20,12*m*p*(20*m-1)))


def m2_k_large_hi(p):
    c_lo=F(19,39)
    # M_p and V_p as in the paper (note g(2p) is rational).
    M=(seed_log_hi(p)-log_lo(p+1)/2+F(2*p+1,2)
       -log_lo(g(2*p))/2)
    V=(F(1)+log_pi_hi(F(2)*(F(p)+F(1,2)))/2-log_lo(p+1))/2
    V+=log_hi(20)/78+F(20,936*p)
    eta=F(1,100) if p<=4 else F(1,40)
    # Exact tangent-to-log precondition: C_p <= (1+log(4eta))/2.
    C_hi=(log_hi(p+1)-F(1)
          -log_pi_lo(F(2*p+1)-F(1,20))/2)
    require(C_hi<(F(1)+log_lo(4*eta))/2,
            f'large k log tangent fails at p={p}')
    require(V>0,f'nonpositive V at p={p}')
    return (M+eta+V/40)/(F(p)+c_lo)


def main():
    check_pi()
    require(log_lo(RATE_LO)>THRESH,'winning rate threshold not certified')

    # Uniform seed-dimension tail, all m,k>=2 and p>=20.
    P=20
    require(F_tail_hi(P)<DELTA*P,'universal p-tail base fails')
    Flower=(log_lo(P+1)-log_pi_hi(P)/2+F(33,28*(P+1))
            +F(1,8)+F(1,20)+F(1,36*P))
    require(Flower-P*F_tail_derivative(P)>0,'p-tail monotonicity fails')
    # Analytic F''<0 for p>=20, using p/(p+1)>=20/21.
    require(F(359,882) > (F(33,14)+F(1,18))/20,
            'rational concavity inequality fails')

    # Large product arity for all k>=2, p<=19.
    for p in range(1,20):
        require(m_large_hi(p)<DELTA*p,f'm>=20 tail fails p={p}')

    # Finite product arities 3..19, large join arity k>=20.
    for m in range(3,20):
        c_lo=F(19,20*m-1)
        for p in range(1,20):
            require(k_large_hi(m,p)<DELTA*(F(p)+c_lo),
                    f'k>=20 tail fails m={m}, p={p}')

    # Boundary arities: k=1 yields the seed's product root; m=1,k>=2
    # stays a simplex and tends to e. For k=1 and p>=20 use F tail.
    for p in range(1,20):
        require(seed_log_hi(p)<THRESH*p, f'k=1 boundary fails p={p}')

    # Finite rectangle m>=3.
    rectangle=0
    for m in range(3,20):
        for k in range(2,20):
            for p in range(1,20):
                require(U0_hi(m,k,p)<THRESH,
                        f'finite core fails m={m}, k={k}, p={p}')
                rectangle+=1

    # Product arity m=2: all 2<=k<=19, p<=19.
    for k in range(4,20):
        for p in range(1,20):
            require(U1_hi(2,k,p)<THRESH,
                    f'm=2 first-level core fails k={k},p={p}')
    for p in range(1,20):
        if p==4:
            require(U_refined_hi(2,3,p,2)<THRESH,'(m,k,p)=(2,3,4) fails')
        else:
            require(U1_hi(2,3,p)<THRESH,f'm=2,k=3,p={p} fails')
    for p in range(1,20):
        if p==5:continue  # The unique winning orbit is inherited from 005 v5.
        if p<=7:
            require(U_refined_hi(2,2,p,3)<THRESH,f'm=k=2,p={p} fails')
        else:
            require(U0_hi(2,2,p)<THRESH,f'm=k=2,p={p} fails')

    # Exceptional product arity 2, unbounded join arity >=20.
    for p in range(1,20):
        require(m2_k_large_hi(p)<THRESH,f'm=2 k>=20 fails p={p}')

    print('PASS: all independent homogeneous simplex recursions (m,k,p>=1)')
    print('finite m=3..19,k=2..19,p=1..19:',rectangle,'triples')
    print('finite m=2,k=2..19,p=1..19: 341 competitors + 1 winner')
    print('boundary arities m=1 or k=1: proven; 19 finite simplex seeds checked')
    print('infinite tails: p>=20; m>=20; 3<=m<=19,k>=20; m=2,k>=20')
    print('every competitor log rate < 131/125 < log(14267/5000)')
    print('the winning lower endpoint is pinned to 005 v5, not reproved here')
    print('exact arithmetic: integers/Fraction; verified Machin pi bounds')


if __name__=='__main__':main()
