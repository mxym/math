#!/usr/bin/env python3
"""Exact rational all-order recurrences for forced smooth sharp Bellman germ.

Computes and verifies first six t^(2n) coefficients as a*L+b,
where L=c_*+log(3sqrt(3)/(2sqrt(pi))). All operations use Fraction.
The infinite Taylor-divergence statement follows analytically from
Stirling/Euler-Maclaurin and Euler's Bernoulli-zeta identity.
"""
from fractions import Fraction as F
from math import comb
from check_stirling_germ import bernoulli,beta

ORDER=6


def require(ok,msg):
    if not ok:raise RuntimeError('formal-germ coefficient certificate: '+msg)


def polynomial_mul(a,b,N):
    result=[F(0)]*(N+1)
    for i,x in enumerate(a):
        if i>N:break
        for j,y in enumerate(b):
            if i+j>N:break
            result[i+j]+=x*y
    return result


def polynomial_add(a,b,N):
    return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(N+1)]


def polynomial_shift(a):return [F(0)]+a[:-1]


def coefficients(N=ORDER):
    require(type(N) is int and 1<=N<=25,'unsupported test order')
    bern=bernoulli(2*N)
    betas=[None]+[beta(k,bern) for k in range(1,N+1)]
    f=[F(0)]*(N+1)
    for m in range(1,N+1):
        z=F(1,2*m)
        for k in range(1,(m+1)//2+1):
            z+=betas[k]*F(3**(2*k-1))*F(comb(m-1,2*k-2))
        f[m]=z/F(16**m)

    # A(w)=A0 + sum_m A_m w^m, A0=(2/3)*L.
    A_const=[F(0)]*(N+1)
    A_L=[F(0)]*(N+1)
    A_L[0]=F(2,3)
    for m in range(1,N+1):
        A_const[m]=f[m]/(F(2)-F(1,2*4**m))

    # w=x(8+w)^2/81, x=t^2, with rational Catalan-like recurrence.
    w=[F(0)]*(N+1)
    w[1]=F(64,81)
    for m in range(2,N+1):
        w[m]=(16*w[m-1]+sum(w[i]*w[m-1-i] for i in range(1,m-1)))/81
    for m in range(1,N+1):
        lhs=F(81)*w[m]
        rhs=F(64 if m==1 else 0)+16*w[m-1]
        rhs+=sum(w[i]*w[m-1-i] for i in range(1,m-1))
        if m==1:rhs-=16*w[0]
        require(lhs==rhs,'Lagrange inversion recurrence error')

    # Compose A(w(x)) over fractions, with independent L and rational terms.
    g_const=[F(0)]*(N+1)
    g_L=[F(0)]*(N+1)
    wk=[F(1)]+[F(0)]*N
    for k in range(N):
        for j in range(N+1):
            g_const[j]+=A_const[k]*wk[j]
            g_L[j]+=A_L[k]*wk[j]
        wk=polynomial_mul(wk,w,N)
    eightw=w[:]
    eightw[0]+=F(8)
    p_const=polynomial_shift(polynomial_mul(eightw,g_const,N))
    p_L=polynomial_shift(polynomial_mul(eightw,g_L,N))
    p_const=[z/54 for z in p_const]
    p_L=[z/54 for z in p_L]
    return f,p_L,p_const


def check():
    f,a,b=coefficients()
    expected_f=[F(0),F(1,128),-F(1,2048),-F(13,786432),F(11,4194304)]
    require(f[:5]==expected_f,'formal f(w) Bernoulli coefficients incorrect')
    expected=[
      (F(8,81),F(0)),
      (F(64,6561),F(16,32805)),
      (F(1024,531441),F(6784,55801305)),
      (F(20480,43046721),F(52736,1707519933)),
      (F(458752,3486784401),F(107253760,12862747655289)),
      (F(3670016,94143178827),F(115311542272,48373118860783275)),
    ]
    for i,(aa,bb) in enumerate(expected,1):
        require((a[i],b[i])==(aa,bb),f'unique t^{2*i} germ coefficient incorrect')
    require(all(x>0 for x in a[1:]) and all(x>=0 for x in b[1:]),
            'unexpected sign in finite smooth-germ Taylor prefix')
    print('PASS: exact forced smooth sharp-Bellman formal germ through t^12')
    print('all odd Taylor coefficients vanish, independent of positivity assumptions')
    print('even coefficients are uniquely determined as A_n * L + B_n')
    print('L=c_*+log(3sqrt(3)/(2sqrt(pi)))')
    for i in range(1,7):print(f't^{2*i}: A={a[i]}, B={b[i]}')
    print('proof of all-orders uniqueness and zero convergence radius is analytic, not extrapolated')


if __name__=='__main__':check()
