#!/usr/bin/env python3
"""Exact arithmetic for the wheel real-rootedness criterion."""
from fractions import Fraction as F
from math import comb, gcd
from functools import reduce

checks=0


def check(p):
    global checks
    checks+=1
    if not p:
        raise AssertionError("exact check failed")


def L(a):
    return [x*x-(a[i-1]*a[i+1] if 0<i<len(a)-1 else 0)
            for i,x in enumerate(a)]


def energy(n):
    if n%2:
        p=(n+1)//2
        P0=F(comb(2*p,p),4**p)
        return (2*(n+1)*P0)**2/F(n*(n+3))
    p=n//2
    P0=F(comb(2*p,p),4**p)
    return (F(2*(n+1),n+2)*P0)**2


def narayana(n):
    return [comb(n+1,i)*comb(n+1,i+1)//(n+1) for i in range(n+1)]


def perturbation_bound(n,z):
    e=F(1,2**(n-1))
    n0=sum(c*z**i for i,c in enumerate(narayana(n)))
    n1=e*(-2+(comb(n,2)-2*n)*z+comb(n,3)*z*z)
    n2=e*e*(1+z)
    return n0+min(0,n1)+min(0,n2),n0+max(0,n1)+max(0,n2)


def trim(P):
    while P and not P[-1]:
        P.pop()
    return P


def primitive(P):
    P=trim(P)
    g=reduce(gcd,(abs(x) for x in P),0)
    return [x//g for x in P] if g else []


def pos_scaled_remainder(A,B):
    """Euclidean remainder up to a positive rational multiple."""
    P=A[:]
    while P and len(P)>=len(B):
        d=len(P)-len(B)
        a=P[-1]*(1 if B[-1]>0 else -1)
        P=[abs(B[-1])*p for p in P]
        for j,b in enumerate(B):
            P[d+j]-=a*b
        P=primitive(P)
    return P


def variation(seq):
    seq=[c>0 for c in seq if c]
    return sum(p!=q for p,q in zip(seq,seq[1:]))


def negative_root_count(A):
    B=[i*A[i] for i in range(1,len(A))]
    S=[A,B]
    while B:
        R=[-r for r in pos_scaled_remainder(A,B)]
        if not R:
            break
        S.append(R)
        A,B=B,R
    v_inf=variation([P[-1]*(-1)**(len(P)-1) for P in S])
    v_0=variation([P[0] for P in S])
    return v_inf-v_0


def main():
    for n in range(3,81):
        a=[comb(n,k) for k in range(n+1)]
        check(L(a)==narayana(n))
        check(energy(n)>=F(1,(n+2)**2))
        for d in (F(0),F(1,2**(n-1)),F(1,3**(n-1))):
            b=a[:]
            b[0]-=d
            b[1]-=d
            C=narayana(n)
            C[0]+=-2*d+d*d
            C[1]+=(comb(n,2)-2*n)*d+d*d
            C[2]+=comb(n,3)*d
            check(L(b)==C)
    for n in range(6,11):
        e=F(1,2**(n-1))
        M=max(F(2),F(abs(n-5),2),F(n-2,3))
        check(((n+1)*e*(M+e))**2<energy(n))
    check(11*12*13 < 2**11)
    fixtures={3:[-3,F(-1,2),0],
              4:[-7,-1,F(-1,2),0],
              5:[-3,-2,F(-1,2),F(-1,3),0]}
    for n,Z in fixtures.items():
        for i,z in enumerate(Z):
            lo,hi=perturbation_bound(n,F(z))
            want=(-1)**(n-1-i)
            check(lo>0 if want==1 else hi<0)
    for c in (2,3,4):
        for n in range(3,33):
            a=[comb(n,k)*c**(n-k) for k in range(n+1)]
            a[0]-=c
            a[1]-=1
            check(negative_root_count(L(a))==n)
    # Independently test the sufficient range for cones over unicyclic graphs.
    for n,s in [(20,1),(20,2),(24,4),(28,8),(32,12)]:
        N,S=n+s,s+1
        check((N+1)*(2*N+3)*(N+2)*2**S < 2**(n-1))
        a=[comb(N,k)*2**(N-k) for k in range(N+1)]
        for k in range(S+1):
            a[k]-=comb(S,k)*2**(S-k)
        check(negative_root_count(L(a))==N)
    # Compare with exact known cycle failures at delta=1.
    a=[comb(17,i) for i in range(18)]
    a[0]-=1
    a[1]-=1
    check(L(L(L(a)))[2]==-28272276537344)
    print(f"Wheel certificate: {checks} exact assertions; "
          "95 signed Sturm counts, including five cones over unicyclic graphs.")


if __name__=="__main__":
    main()
