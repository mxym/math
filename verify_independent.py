#!/usr/bin/env python3
"""Independent matrix construction, mixed-state tests, and allocation checks."""
from itertools import product
from math import sqrt
import numpy as np

rng=np.random.default_rng(391627)
tol=3e-9
counts={}

def ck(k,v):
    assert np.all(v), k
    counts[k]=counts.get(k,0)+1

def g(a,b):
    a=np.clip(a,0,1)
    b=np.clip(b,0,1)
    return np.where(a>=b,1,(np.sqrt(a*b)+np.sqrt((1-a)*(1-b)))**2)

def adj(A):
    return A.conj().T

def prepare(P,b):
    result=[]
    for x,bx in enumerate(b):
        e=np.eye(len(P),dtype=P.dtype)[:,x]
        f=P@e
        a=np.linalg.norm(f)**2
        if a+1e-12>=bx:
            psi=e
        elif a<1e-12:
            z=np.argmax(np.linalg.norm(P,axis=0))
            psi=np.sqrt(bx)*P[:,z]/np.linalg.norm(P[:,z])+np.sqrt(1-bx)*e
        else:
            psi=np.sqrt(bx)*f/np.linalg.norm(f)+np.sqrt(1-bx)*(e-f)/np.linalg.norm(e-f)
        ck("prepared states normalized",abs(np.vdot(psi,psi)-1)<tol)
        ck("population and exact success",np.vdot(psi,P@psi).real>=bx-tol
           and abs(abs(psi[x])**2-g(a,bx))<tol)
        result.append(abs(psi[x])**2)
    return np.array(result)

def projection_of_diagonal(a):
    # Independent reverse elimination implementation: store a sequence of
    # plane rotations, start at a 0/1 diagonal, and apply them backwards.
    a=np.array(a,dtype=float).copy()
    rotations=[]
    while len(idx:=np.flatnonzero((a>1e-12)&(a<1-1e-12)))>0:
        assert len(idx)>=2
        i,j=idx[0],idx[-1]
        s=a[i]+a[j]
        hi,lo=min(s,1),max(0,s-1)
        mix=(a[i]-lo)/(hi-lo)
        cs=max(0,min(1,mix))
        rotations.append((i,j,sqrt(cs),sqrt(1-cs)))
        a[i],a[j]=hi,lo
    P=np.diag(np.rint(a))
    for i,j,c,s in reversed(rotations):
        R=np.eye(len(a))
        R[i,i]=R[j,j]=c
        R[i,j],R[j,i]=-s,s
        P=R@P@R.T
    return P

for n in range(2,16):
    U=np.exp(2j*np.pi*np.outer(np.arange(n),np.arange(n))/n)/sqrt(n)
    for d in range(1,n):
        P=U[:,:d]@adj(U[:,:d])
        a=d/n
        for eps in [0,(1-a)/4,(1-a)/2,1-a,(2-a)/2,1]:
            ys=prepare(P,np.full(n,1-eps))
            ck("Fourier normalized optimum",np.ptp(ys)<tol
               and abs(ys.mean()-g(a,1-eps))<tol)

def grad_a(a,b):
    return 2*b-1+(1-2*a)*sqrt(b*(1-b)/(a*(1-a)))

def best_allocation(p,b,d):
    if b.sum()<=d:
        a=b.copy()
        spare=d-a.sum()
        for x in range(len(a)):
            delta=min(1-a[x],spare)
            a[x]+=delta
            spare-=delta
        return a,0
    def near(mu,tie_mode):
        A=np.zeros(len(p))
        for i,(w,B) in enumerate(zip(p,b)):
            if B==1:
                A[i]=float(w>mu or (w==mu and tie_mode))
            elif B>0:
                z=mu/w-(2*B-1)
                A[i]=(1-z/sqrt(z*z+4*B*(1-B)))/2
        return A
    for mu in set(p[b==1]):
        lo,hi=near(mu,False),near(mu,True)
        if lo.sum()-1e-12<=d<=hi.sum()+1e-12:
            spare=d-lo.sum()
            for i in np.flatnonzero(hi-lo):
                delta=max(0,min(1,spare))
                lo[i]+=delta
                spare-=delta
            return lo,mu
    lo,hi=0,1
    while near(hi,False).sum()>d:
        hi*=2
    for k in range(85):
        m=(lo+hi)/2
        if near(m,False).sum()>d:
            lo=m
        else:
            hi=m
    return near((lo+hi)/2,False),(lo+hi)/2

for q in range(120):
    n=3 if q<60 else 4
    d=1 if n==3 else 2
    p=rng.dirichlet(np.ones(n))
    b=rng.uniform(0,1,n)
    if q%3==0:
        b[0]=1
    if q%5==0:
        b[1]=0
    if q%13==0:
        b[:]=1
    a,mu=best_allocation(p,b,d)
    ck("allocation feasibility",abs(a.sum()-d)<tol and a.min()>=-tol
       and a.max()<=1+tol)
    if mu>0:
        assert np.all(a<=b+tol)
        for i,(ax,bx) in enumerate(zip(a,b)):
            if 1e-6<ax<bx-1e-6 and bx<1:
                ck("independent marginal balance",abs(p[i]*grad_a(ax,bx)-mu)<1e-7)
    P=projection_of_diagonal(a)
    ck("real projection reconstruction",np.linalg.norm(P@P-P)<tol
       and np.linalg.norm(np.diag(P)-a)<tol)
    success=p@prepare(P,b)
    # Compare with brute search over a separate fixed lattice, including ties.
    m=18
    grid=[]
    for z in product(range(m+1),repeat=n-1):
        last=d*m-sum(z)
        if 0<=last<=m:
            grid.append([*z,last])
    grid=np.array(grid)/m
    grid_best=np.max(g(grid,b)@p)
    ck("closed allocation dominates independent grid",success+tol>=grid_best)

def rand_complex(a,b):
    return rng.normal(size=(a,b))+1j*rng.normal(size=(a,b))

def branch(n,d,D):
    W=np.linalg.qr(rand_complex(D,d))[0]
    P=W@adj(W)
    blocks=[rand_complex(D,D) for _ in range(n)]
    pov=[A@adj(A) for A in blocks]
    e,U=np.linalg.eigh(sum(pov))
    C=(U*(e**(-1/2)))@adj(U)
    pov=[C@M@C for M in pov]
    S=[]
    A=[]
    B=[]
    for M in pov:
        U=rand_complex(D,int(rng.integers(1,D+1)))
        rho=U@adj(U)
        rho/=np.trace(rho).real
        yi=np.trace(M@rho).real
        ai=min(1,np.trace(P@M).real)
        bi=np.trace(P@rho).real
        ck("actual mixed-state POVM bound",yi<=g(ai,bi)+tol)
        S.append(yi)
        A.append(ai)
        B.append(bi)
    ck("POVM subspace budget",sum(A)<=d+tol)
    return np.array([S,A,B])

for _ in range(120):
    n=int(rng.integers(3,8))
    d=int(rng.integers(1,n))
    r0=branch(n,d-1,n+1)
    r1=branch(n,d+1,n+2)
    S,A,B=(r0+r1)/2
    ck("averaged independent flags for each label",S<=g(A,B)+tol)
    ck("uniform-label mean bound under flags",S.mean()<=g(d/n,B.mean())+tol)

# Independence of the flag and the COMMON nature of the subspace matter.
# Perfect guessing from a label-revealing flag, or from a label-specific
# rank-one projector, is outside the theorem at d=1 and eps=0.
n=4
flag_success=np.trace(np.eye(n))/n
same_signal_population=1
assert flag_success==1 and same_signal_population==1 and g(1/n,1)<1
print("negative control: label-dependent flags are outside the model")
for k,n in counts.items():
    print(f"{k}: {n}")
