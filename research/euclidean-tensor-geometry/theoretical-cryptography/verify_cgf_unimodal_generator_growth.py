#!/usr/bin/env python3
"""Exact coefficient and normal-form checks for the unimodal CGF note."""
from collections import defaultdict
from functools import lru_cache
from math import gcd

if not __debug__:
    raise RuntimeError("run without Python -O")

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                c[i+j]+=x*y
    return tuple(c)

def div(a,b):
    """Exact monic division in Z[q], using ascending coefficients."""
    if len(a)<len(b):
        raise ArithmeticError
    a=list(a)
    c=[0]*(len(a)-len(b)+1)
    for i in range(len(c)-1,-1,-1):
        v=a[i+len(b)-1]
        c[i]=v
        for j,y in enumerate(b):
            a[i+j]-=v*y
    if any(a):
        raise ArithmeticError
    return tuple(c)

@lru_cache(None)
def phi(m):
    a=(-1,)+(0,)*(m-1)+(1,)
    for d in range(1,m):
        if m%d==0:
            a=div(a,phi(d))
    return a

def uni(a):
    return a[0]==1 and a==a[::-1] and all(a[j]<=a[j+1] for j in range((len(a)-1)//2))

def lc(a):
    return all(a[j]*a[j]>=a[j-1]*a[j+1] for j in range(1,len(a)-1))

def qint(k):
    return (1,)*k

def sparse(k):
    return (1,)+(0,)*(k-1)+(1,)

def T(k,h=1):
    return mul(sparse(k),qint(k+h))

def near_expected(m,d):
    if d==m-1:
        return {qint(m)}
    if d==m:
        U={mul(qint(m),qint(2))}
        if m%2==0 and m>=4:
            U.add(T(m//2))
        return U
    if d==m+1:
        U={mul(qint(m),(1,j,1)) for j in (0,1,2)}
        if m%2==0 and m>=6:
            U|={T(m//2,2),mul(T(m//2),qint(2))}
        return U
    raise ValueError((m,d))

def near_log_concave(m,d):
    if d==m-1:
        return {qint(m)}
    if d==m:
        return {mul(qint(m),qint(2))}
    s={mul(qint(m),(1,j,1)) for j in (1,2)}
    if m==2:
        s.add(qint(4))
    return s

def check_near(N=20):
    # Include even large roots with totient <= N: phi(m)^2 >= m/2.
    # This does not assume the angular root exclusion from the proof.
    P=[]
    for m in range(2,2*N*N+1):
        degree=sum(gcd(j,m)==1 for j in range(1,m+1))
        if degree<=N:
            p=phi(m)
            assert len(p)==degree+1
            P.append((m,degree,p))
    count=[0]*(N+1)
    UC=[0]*(N+1)
    LC=[0]*(N+1)
    by=defaultdict(set)
    flags=set()
    def walk(p,begin,degree):
        count[degree]+=1
        if uni(p):
            UC[degree]+=1
            LC[degree]+=int(lc(p))
            assert all(m<=degree+1 for m in flags)
            for m in range(max(2,degree-1),degree+2):
                if m in flags:
                    by[m,degree].add(p)
        for j in range(begin,len(P)):
            m,e,q=P[j]
            if degree+e<=N:
                fresh=m not in flags
                flags.add(m)
                walk(mul(p,q),j,degree+e)
                if fresh:
                    flags.remove(m)
    walk((1,),0,0)
    cases=0
    for m in range(2,N+2):
        for d in (m-1,m,m+1):
            if d<=N:
                got=by[m,d]
                assert got==near_expected(m,d),(m,d,got)
                assert {p for p in got if lc(p)}==near_log_concave(m,d),(m,d)
                cases+=1
    print("unrestricted cyclotomic products / unimodal / log-concave:",sum(count),sum(UC),sum(LC))
    print("near-root (order, degree) classifications:",cases)

def check_monoid(N=24):
    G=[]
    dim=N+3
    for k in range(2,N+2):
        if k-1<=N:
            c=[0]*dim;c[k]=1
            G.append((k-1,tuple(c),qint(k)))
        if 2*k<=N:
            c=[0]*dim;c[2*k]=1;c[k+1]=1;c[k]=-1
            assert sum(k*x-x for k,x in enumerate(c))==2*k
            G.append((2*k,tuple(c),T(k)))
    monoid=[{} for _ in range(N+1)]
    monoid[0][(0,)*dim]=(1,)
    for j in range(N+1):
        for a,p in monoid[j].items():
            for w,b,q in G:
                if j+w>N:
                    continue
                key=tuple(x+y for x,y in zip(a,b))
                r=mul(p,q)
                assert uni(r)
                before=monoid[j+w].setdefault(key,r)
                assert before==r
    # Direct coefficient enumeration deduplicates independently of signed
    # exponent representation.
    for pool in monoid:
        assert len(set(pool.values()))==len(pool)
    e=[1]+[0]*N
    for j in range(1,N+1):
        mult=1+(j%2==0)-(j%3==2)
        for _ in range(mult):
            for i in range(j,N+1):
                e[i]+=e[i-j]
    assert [len(pool) for pool in monoid]==e
    # Recover the canonical representation of every stored exponent vector.
    for d,pool in enumerate(monoid):
        for key,p in pool.items():
            a=[0]*dim
            t=[0]*dim
            for m in range(2,dim):
                incoming=t[m-1]+(t[m//2] if m%2==0 else 0)
                h=key[m]-incoming
                a[m]=max(0,h)
                t[m]=max(0,-h)
            assert sum((k-1)*a[k]+2*k*t[k] for k in range(2,dim))==d
            r=(1,)
            for k in range(2,dim):
                for _ in range(a[k]):
                    r=mul(r,qint(k))
                for _ in range(t[k]):
                    r=mul(r,T(k))
            assert r==p
    t=0
    for d in range(0,13):
        for p in monoid[d].values():
            for k in range(2,9):
                z=(0,)*(k-1)
                r=tuple(x for y in p for x in ((y,)+z))
                r=r[:k*d+1]
                padded=mul(r,qint(k))
                for D in [0,*range(2,(2*k if d%2 else k)+1)]:
                    h=mul(padded,sparse(D)) if D else padded
                    assert uni(h) and h[1]==1
                    assert len(h)-1==k*(d+1)-1+D
                    t+=1
    print("normal-form polynomial counts by degree:",e)
    print("all distinct submonoid polynomials:",sum(e))
    print("exact atom inflation checks:",t)

if __name__=="__main__":
    check_near()
    check_monoid()
    print("PASS")
