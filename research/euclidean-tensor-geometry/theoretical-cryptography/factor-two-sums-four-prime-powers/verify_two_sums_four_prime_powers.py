#!/usr/bin/env python3
from itertools import combinations, product
from math import gcd, isqrt

def primes_upto(n):
    a=[True]*(n+1)
    a[0]=a[1]=False
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=[False]*(((n-p*p)//p)+1)
    return [i for i,v in enumerate(a) if v]

PRIMES=primes_upto(60)

def phi_fac(fac):
    z=1
    for p,a in fac:
        z*=p**(a-1)*(p-1)
    return z

def value(fac):
    z=1
    for p,a in fac:
        z*=p**a
    return z

def ceil_log2(n):
    return (n-1).bit_length()

def geom(p,t):
    return (p**t-1)//(p-1)

def sigma_power(fac,J):
    z=1
    for p,a in fac:
        z*=geom(p,a*J+1)
    return z

def add(a,b):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a):
        c[i]+=x
    for i,x in enumerate(b):
        c[i]+=x
    while len(c)>1 and c[-1]==0:
        c.pop()
    return c

def scale(a,k):
    return [k*x for x in a]

def zeq(a):
    return [0]+a

def q_polynomial(u,A):
    # Q_A(Z)=G_{A+1}(p)G_{A+1}(q), p+q=Z, pq=u.
    # L_d=p^d+q^d obeys L_d=ZL_{d-1}-uL_{d-2}.
    L=[[2],[0,1]]
    for _ in range(2,A+1):
        L.append(add(zeq(L[-1]),scale(L[-2],-u)))
    Q=[sum(u**j for j in range(A+1))]
    for d in range(1,A+1):
        h=sum(u**j for j in range(A-d+1))
        Q=add(Q,scale(L[d],h))
    assert len(Q)==A+1 and Q[-1]==1
    return Q

def peval(a,x):
    z=0
    for c in reversed(a):
        z=z*x+c
    return z

def bareiss(M):
    A=[row[:] for row in M]
    n=len(A)
    if n==0:
        return 1
    sign=1
    prev=1
    for k in range(n-1):
        if A[k][k]==0:
            s=next((i for i in range(k+1,n) if A[i][k]),None)
            if s is None:
                return 0
            A[k],A[s]=A[s],A[k]
            sign=-sign
        pivot=A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                A[i][j]=(A[i][j]*pivot-A[i][k]*A[k][j])//prev
        for i in range(k+1,n):
            A[i][k]=0
        prev=pivot
    return sign*A[-1][-1]

def resultant(a,b):
    # Ascending coefficient lists.
    while len(a)>1 and a[-1]==0:
        a.pop()
    while len(b)>1 and b[-1]==0:
        b.pop()
    m=len(a)-1
    n=len(b)-1
    ad=list(reversed(a))
    bd=list(reversed(b))
    S=[]
    for i in range(n):
        S.append([0]*i+ad+[0]*(n-1-i))
    for i in range(m):
        S.append([0]*i+bd+[0]*(m-1-i))
    return bareiss(S)

floor_cases=0
for k in range(1,5):
    for ps in combinations(PRIMES[:8],k):
        for exps in product(range(1,4),repeat=k):
            fac=list(zip(ps,exps))
            n=value(fac)
            J=max(2,ceil_log2(n))
            S=sigma_power(fac,J)
            assert n**(J+1)//S==phi_fac(fac)
            floor_cases+=1

branch_counts={}
classification_cases=0
for ps in combinations(PRIMES[:9],4):
    for exps in product(range(1,4),repeat=4):
        fac=list(zip(ps,exps))
        n=value(fac)
        ph=phi_fac(fac)
        M=ceil_log2(n)
        r=n//gcd(n,ph)
        U=gcd(n,r**M)
        V=n//U
        su=[(p,a) for p,a in fac if r%p==0]
        sv=[(p,a) for p,a in fac if r%p!=0]
        assert su and len(su)+len(sv)==4
        if len(su)==1 or len(sv)==1:
            cat="prime-power side"
        elif V==1:
            groups={}
            for p,a in su:
                groups.setdefault(a,[]).append(p)
            sizes=sorted(map(len,groups.values()))
            if sizes==[4]:
                cat="equal quartic"
            elif 1 in sizes:
                cat="singleton exponent group"
            else:
                assert sizes==[2,2]
                cat="two semiprime groups"
        else:
            assert len(su)==len(sv)==2
            cat=("split known support" if su[0][1]!=su[1][1]
                 else "known semiprime block")
        branch_counts[cat]=branch_counts.get(cat,0)+1
        classification_cases+=1

elim_cases=[
    (2,3,5,7,1,1,2),
    (3,5,2,7,2,1,2),
    (5,11,2,3,1,2,3),
    (7,13,2,5,2,3,1),
    (7,11,2,3,1,1,2),
    (5,13,2,7,2,2,1),
]
clearing_cases=0
e1_cases=0
for p,q,x,y,a,c,d in elim_cases:
    n=(p*q)**a*x**c*y**d
    J=max(2,ceil_log2(n))
    A=a*J
    u=p*q
    V=x**c*y**d
    ph=(u**(a-1)*(p-1)*(q-1)*
        x**(c-1)*(x-1)*y**(d-1)*(y-1))
    S=(geom(p,A+1)*geom(q,A+1)*
       geom(x,c*J+1)*geom(y,d*J+1))
    C=ph//u**(a-1)
    D=x**(c-1)*y**(d-1)*(x-1)*(y-1)
    Q=q_polynomial(u,A)
    assert peval(Q,p+q)==geom(p,A+1)*geom(q,A+1)
    W=(u+1)*D-C
    Qtilde=sum(co*D**(A-h)*W**h for h,co in enumerate(Q))
    assert D**A*S-geom(x,c*J+1)*geom(y,d*J+1)*Qtilde==0
    clearing_cases+=1

    # At X=1 the nonzero part of E(1) is
    # Res_Y(Y^d-V,G_{dJ+1}(Y)).
    f=[-V]+[0]*(d-1)+[1]
    gt=[1]*(d*J+1)
    assert resultant(f,gt)!=0
    e1_cases+=1

quartic_cases=0
coprime_index_cases=0
for ps in combinations(PRIMES[:9],4):
    m=1
    for p in ps:
        m*=p
    for a in range(1,4):
        n=m**a
        J=max(2,ceil_log2(n))
        t1=a*J+1
        t2=2*a*J+1
        assert gcd(t1,t2)==1
        S1=S2=1
        for p in ps:
            S1*=geom(p,t1)
            S2*=geom(p,t2)
        assert S1==sigma_power([(p,a) for p in ps],J)
        assert S2==sigma_power([(p,a) for p in ps],2*J)
        quartic_cases+=1
        coprime_index_cases+=1

print("PASS")
print("totient-floor cases:",floor_cases)
print("gcd/equal-order classification cases:",classification_cases)
print("classification counts:",sorted(branch_counts.items()))
print("2+2 clearing identities:",clearing_cases)
print("2+2 E(1) nonzero resultants:",e1_cases)
print("equal-quartic exact two-resultant cases:",quartic_cases)
print("coprime effective-index cases:",coprime_index_cases)
