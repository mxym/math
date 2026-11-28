#!/usr/bin/env python3
from itertools import combinations, product
from math import ceil, log2, isqrt, gcd, comb

def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def det_bareiss(A):
    A=[list(map(int,r)) for r in A];n=len(A)
    if not n:return 1
    sign=1;prev=1
    for k in range(n-1):
        if A[k][k]==0:
            z=next((i for i in range(k+1,n) if A[i][k]),None)
            if z is None:return 0
            A[k],A[z]=A[z],A[k];sign=-sign
        p=A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                A[i][j]=(A[i][j]*p-A[i][k]*A[k][j])//prev
        prev=p
        for i in range(k+1,n):A[i][k]=0
    return sign*A[-1][-1]

def resultant(f,g):
    f=trim(f[:]);g=trim(g[:]);m=len(f)-1;n=len(g)-1
    A=list(reversed(f));B=list(reversed(g));M=[]
    for i in range(n):M.append([0]*i+A+[0]*(n-1-i))
    for i in range(m):M.append([0]*i+B+[0]*(m-1-i))
    return det_bareiss(M)

def sigma_pp(p,e):
    return (p**(e+1)-1)//(p-1)

def poly_H(w,psi,a,b):
    d=w-psi
    h=[0]*(a+b+1)
    c=w**(b-1)
    for j in range(b+1):
        h[a+j]+=c*comb(b,j)*(-1)**(b-j)
    for j in range(b+1):
        h[j]-=comb(b,j)*d**j*(-w)**(b-j)
    while len(h)>1 and h[-1]==0:h.pop()
    return h

def peval(f,x):
    z=0
    for c in reversed(f):z=z*x+c
    return z

primes=[2,3,5,7,11]
floor_cases=0
for k in [1,2,3]:
    for ps in combinations(primes,k):
        for es in product(range(1,4),repeat=k):
            n=1;phi=1;S=1
            for p,a in zip(ps,es):
                n*=p**a;phi*=p**(a-1)*(p-1)
            J=max(2,ceil(log2(n)))
            for p,a in zip(ps,es):S*=sigma_pp(p,a*J)
            assert n**(J+1)//S==phi
            floor_cases+=1


two_prime_H=0
for p,q in combinations(primes,2):
    for a,b in product(range(1,4),repeat=2):
        w=p**a*q**b
        psi=p**(a-1)*(p-1)*q**(b-1)*(q-1)
        H=poly_H(w,psi,a,b)
        assert len(H)-1==a+b and peval(H,p)==0
        d=w-psi
        assert d*p-w!=0 and w*(p-1)//(d*p-w)==q
        two_prime_H+=1

split_total=split_vpos=split_vzero=0
split_prime_triples=list(combinations(primes,3))+list(combinations([5,7,13,17,19],3))
for ps in split_prime_triples:
    for es in product(range(1,4),repeat=3):
        n=1;phi=1
        for p,a in zip(ps,es):
            n*=p**a;phi*=p**(a-1)*(p-1)
        M=ceil(log2(n));r0=n//gcd(n,phi)
        U=gcd(n,r0**M);V=n//U
        assert U*V==n and gcd(U,V)==1
        if V>1:
            wu=sum(U%p==0 for p in ps);wv=sum(V%p==0 for p in ps)
            assert min(wu,wv)==1
            split_vpos+=1
        else:
            assert r0==ps[0]*ps[1]*ps[2]
            A=[1]+[gcd(n,r0**j) for j in range(1,max(es)+2)]
            w=[A[j]//A[j-1] for j in range(1,len(A))]
            groups=[w[j-1]//w[j] for j in range(1,max(es)+1)]
            assert __import__('math').prod(g**(i+1) for i,g in enumerate(groups))==n
            split_vzero+=1
        split_total+=1

# If two exponent classes occur as a 2+1 split, the known singleton
# supplied by equal-order decomposition determines phi of the double group.
split_cases=0
for ps in combinations(primes,3):
    p,q,r=ps
    for e in range(1,4):
        for f in range(1,4):
            if e==f:continue
            u=p*q
            n=u**e*r**f
            phi=(u**(e-1)*(p-1)*(q-1))*(r**(f-1)*(r-1))
            phi_u=phi//(u**(e-1)*r**(f-1)*(r-1))
            assert phi_u==(p-1)*(q-1)
            sm=u-phi_u+1
            disc=sm*sm-4*u
            z=isqrt(disc)
            assert z*z==disc and {(sm-z)//2,(sm+z)//2}=={p,q}
            split_cases+=1

# Uniform multiplicity: exact cyclic resultant and leading coefficient.
uniform_cases=0
for ps in combinations([2,3,5,7],3):
    p,q,r=ps;m=p*q*r;phi_m=(p-1)*(q-1)*(r-1);s=p+q+r
    C=m-phi_m-1
    for a in [1,2]:
        n=m**a;J=max(2,ceil(log2(n)));t=a*J+1
        S=sigma_pp(p,a*J)*sigma_pp(q,a*J)*sigma_pp(r,a*J)
        P=[-m,s+C,-s,1]
        assert resultant(P,[1]*t)==S
        uniform_cases+=1

leading_cases=0
for t in range(2,41):
    D=t-1
    lead=(-1)**(3*D)*resultant([1]*t,[0,1,-1])
    assert lead==t
    leading_cases+=1

# Large uniform identity without a large Sylvester determinant.
p,q,r,a=1009,1013,1019,7
m=p*q*r;n=m**a;J=max(2,ceil(log2(n)));t=a*J+1
S=sigma_pp(p,a*J)*sigma_pp(q,a*J)*sigma_pp(r,a*J)
assert S==sum(p**i for i in range(t))*sum(q**i for i in range(t))*sum(r**i for i in range(t))

print("PASS")
print("arbitrary-multiplicity totient-floor cases:",floor_cases)
print("two-prime eliminant cases:",two_prime_H)
print("gcd/equal-order split cases:",split_total,split_vpos,split_vzero)
print("nonuniform 2+1 completion cases:",split_cases)
print("uniform exact resultant cases:",uniform_cases)
print("uniform leading-coefficient cases:",leading_cases)
print("large uniform n/t/S bits:",n.bit_length(),t,S.bit_length())
