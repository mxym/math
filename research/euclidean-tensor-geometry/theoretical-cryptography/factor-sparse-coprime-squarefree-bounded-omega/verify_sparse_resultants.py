#!/usr/bin/env python3
from itertools import product, combinations
from math import ceil, log2, factorial, gcd

def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def det_bareiss(A):
    A=[list(map(int,r)) for r in A]
    n=len(A)
    if n==0:return 1
    sign=1; prev=1
    for k in range(n-1):
        if A[k][k]==0:
            z=next((i for i in range(k+1,n) if A[i][k]),None)
            if z is None:return 0
            A[k],A[z]=A[z],A[k];sign=-sign
        pivot=A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                A[i][j]=(A[i][j]*pivot-A[i][k]*A[k][j])//prev
        prev=pivot
        for i in range(k+1,n):A[i][k]=0
    return sign*A[-1][-1]

def resultant(f,g):
    f=trim(f[:]);g=trim(g[:])
    a=list(reversed(f));b=list(reversed(g))
    m=len(f)-1;n=len(g)-1
    M=[]
    for i in range(n):M.append([0]*i+a+[0]*(n-1-i))
    for i in range(m):M.append([0]*i+b+[0]*(m-1-i))
    return det_bareiss(M)

def div_x_minus_1(q):
    # ascending q, exact division by x-1
    d=len(q)-1
    out=[0]*d
    out[-1]=q[-1]
    for i in range(d-2,-1,-1):out[i]=q[i+1]+out[i+1]
    assert q[0]==-out[0]
    return trim(out)

def P_coeffs(k,n,phi,e,t=1):
    # ascending coefficients of x^k-e1*x^(k-1)+...+(-1)^k*n
    es=[1]+[t*x for x in e]
    c=(-1)**k*phi-1-(-1)**k*n-sum(((-1)**j)*es[j] for j in range(1,k-1))
    e_last=(-1)**(k-1)*c
    es += [e_last,n]
    return [((-1)**(k-i))*es[k-i] for i in range(k+1)]

def Q_coeffs(k,v):
    q=[0]*(k-1)
    for j,x in enumerate(v,1):
        s=(-1)**j*x
        q[k-j-1]+=s
        q[0]-=s
    return trim(q)

def leading_by_differences(vals):
    a=list(vals)
    while len(a)>1:a=[a[i+1]-a[i] for i in range(len(a)-1)]
    return a[0]//factorial(len(vals)-1)

lead_cases=0
for k,ms in [(3,[5]),(4,[3,5]),(5,[2,3,5]),(6,[2,3,5,7])]:
    for m in ms:
        g=[1]*m;d=m-1
        for v in product(range(-2,3),repeat=k-2):
            if not any(v):continue
            vals=[resultant(P_coeffs(k,30+k,7+k,v,t),g) for t in range(d+1)]
            got=leading_by_differences(vals)
            R=div_x_minus_1(Q_coeffs(k,v))
            want=(-1)**(k*d)*m*resultant(g,R)
            assert got==want,(k,m,v,got,want)
            lead_cases+=1

def inv(a,p):return pow(a,p-2,p)
def canon(v,p):
    for x in v:
        if x%p:
            z=inv(x%p,p);return tuple((y*z)%p for y in v)
    raise AssertionError
def poly_eval(a,x,p):
    z=0
    for c in reversed(a):z=(z*x+c)%p
    return z

projective=0
for k,ms,p in [(4,[3,5],31),(5,[2,3,5],31)]:
    roots={}
    for m in ms:
        roots[m]=[z for z in range(1,p) if pow(z,m,p)==1 and z!=1]
        assert len(roots[m])==m-1
    seen=set()
    for v in product(range(p),repeat=k-2):
        if not any(v):continue
        c=canon(v,p)
        if c in seen:continue
        seen.add(c);projective+=1
        q=Q_coeffs(k,c)
        assert any(all(poly_eval(q,z,p)!=0 for z in roots[m]) for m in ms)

primes=[2,3,5,7,11,13]
floor_cases=0;equation_cases=0
for k in range(1,6):
    for ps in combinations(primes,k):
        n=1
        for p in ps:n*=p
        M=ceil(log2(n));J=max(2,M)
        S=1
        for p in ps:S*=sum(p**a for a in range(J+1))
        phi=1
        for p in ps:phi*=p-1
        assert n**(J+1)//S==phi
        floor_cases+=1
        if k>=3:
            e=[]
            for j in range(1,k):
                s=0
                for cs in combinations(ps,j):
                    z=1
                    for p in cs:z*=p
                    s+=z
                e.append(s)
            P=P_coeffs(k,n,phi,e[:-1],1)
            for m in [2,3,5,7][:k-2]:
                assert resultant(P,[1]*m)==__import__('math').prod(sum(p**a for a in range(m)) for p in ps)
                equation_cases+=1

print("PASS")
print("leading-form exact cases:",lead_cases)
print("finite-field projective points:",projective)
print("high-power totient-floor cases:",floor_cases)
print("true sparse-resultant equations:",equation_cases)
