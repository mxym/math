#!/usr/bin/env python3
"""Exact controls for the alternating-ring Walsh certificate and explicit laws."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import prod

Z=(F(0),F(0));ONE=(F(1),F(0))
def require(test,msg):
    if not test:raise AssertionError(msg)
def plus(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def star(a):return (a[0],-a[1])
def times(a,b):return (a[0]*b[0]-a[1]*b[1],a[1]*b[0]+a[0]*b[1])
def sq(a):return a[0]**2+a[1]**2
def mul(A,B):
    C=[[Z]*len(A) for _ in A]
    for i,row in enumerate(A):
        for j,a in enumerate(row):
            if a!=Z:
                for k,b in enumerate(B[j]):
                    if b!=Z:C[i][k]=plus(C[i][k],times(a,b))
    return C
def det(A,I,J):
    z=Z
    for perm in permutations(J):
        r=ONE
        for i,j in zip(I,perm):
            r=times(r,A[i][j])
            if r==Z:break
        if sum(a>b for a,b in combinations(perm,2))%2:r=neg(r)
        z=plus(z,r)
    return z
def ring(n,matches,params):
    M=[[Z]*n for _ in range(n)]
    for (i,j),(c,s,phase) in zip(matches,params):
        M[i][i]=(c,F(0));M[i][j]=(s,F(0))
        M[j][i]=times((-s,F(0)),phase); M[j][j]=times((c,F(0)),phase)
    return M
def perm_bits(n,A,B,b):
    m=len(A);P=list(range(n));Q=list(range(n))
    for (u,v),x in zip(A,b[:m]):
        if x:P[u],P[v]=v,u
    for (u,v),x in zip(B,b[m:]):
        if x:Q[u],Q[v]=v,u
    return [Q[P[i]] for i in range(n)]

def check(m,params,choose_tau):
    n=2*m
    A=[(2*i,2*i+1) for i in range(m)]
    B=[(2*i+1,(2*i+2)%n) for i in range(m)]
    V=ring(n,A,params[:m]);W=ring(n,B,params[m:]);U=mul(W,V)
    C=ONE
    for i,j in A:C=times(C,times(V[i][i],star(V[j][i])))
    for i,j in B:C=times(C,times(W[j][j],star(W[j][i])))
    D=(-1)**(m-1)*C[0]
    ps=[c*c for c,s,z in params]
    qs=[]
    for b in product((0,1),repeat=n):
        default=prod(1-p if x else p for p,x in zip(ps,b))
        if choose_tau:
            x=(1-ps[0])/ps[0]; X=max(x,1/x)
            tau=(X**-2-1)/2
            if x<1:tau=-tau
            E=D*tau/2
        else:E=F(0)
        q=default+(-1)**sum(b)*(D+E*(n-2*sum(b)))
        require(q>=0,"probability nonnegative")
        qs.append((perm_bits(n,A,B,b),q))
    require(sum(q for pi,q in qs)==1,"probability total")
    controls=0
    for k in range(m+1):
        masks=list(combinations(range(n),k))
        for J in masks:
            mass={}
            for pi,q in qs:
                I=tuple(sorted(pi[j] for j in J))
                mass[I]=mass.get(I,F(0))+q
            for I in masks:
                require(mass.get(I,F(0))==sq(det(U,I,J)),"entire squared-minor law")
                controls+=1
    print("PASS full law",m,controls,"phase",C)

a=(F(4,5),F(3,5),ONE)
b=(F(3,5),F(4,5),ONE)
check(2,[a]*4,True)
check(3,[b]*6,True)
# Distinct diagonals and a nontrivial complex phase with nonzero real part. Only an
# A-layer row phase affects the cross term in this particular gauge.
check(3,[(a[0],a[1],(F(40,401),F(399,401))),b,a,b,a,b],False)
for m,X,expect in [(2,F(10),True),(3,F(2),True),(3,F(3),False),
                   (5,F(4,3),True),(5,F(2),False)]:
    J=m if m%2 else m-1
    valid=J*(1-X**-2)<=2*(1+X**(-J))
    require(valid==expect,"sharp scalar threshold")
    tau=(X**-2-1)/2
    require(all(X**k-(-1 if k%2 else 1)*(1-tau*k)>=0 for k in range(-m,m+1))==valid,
            "one scalar implements the legal law")
print("PASS scalar interval controls")
