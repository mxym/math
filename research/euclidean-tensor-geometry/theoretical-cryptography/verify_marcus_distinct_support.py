#!/usr/bin/env python3
"""Exact controls for distinct-support universal Givens circuits."""
from itertools import combinations, permutations, product
from math import prod
from fractions import Fraction as F


def require(test, msg):
    if not test:
        raise AssertionError(msg)


def ident(n):
    return [[int(i==j) for j in range(n)] for i in range(n)]


def matmul(A,B):
    return [[sum(x*y for x,y in zip(r,c)) for c in zip(*B)] for r in A]


def det(A,I,J):
    M=[[A[i][j] for j in J] for i in I]
    d=1
    s=1
    for k in range(len(M)-1):
        j=next((j for j in range(k,len(M)) if M[j][k]),None)
        if j is None:return 0
        if j!=k:M[j],M[k]=M[k],M[j]; s=-s
        p=M[k][k]
        for i in range(k+1,len(M)):
            for j in range(k+1,len(M)):
                q,r=divmod(M[i][j]*p-M[i][k]*M[k][j],d)
                require(r==0,"Bareiss exact division")
                M[i][j]=q
        d=p
    return s*M[-1][-1] if M else 1


Q=list(permutations(range(4)))
def pair(s):
    return tuple(int(c)-1 for c in s)
def key(w):
    return ''.join(str(v+1) for e in w for v in sorted(e))


def orbit(w):
    seen={tuple(w)};todo=[tuple(w)]
    while todo:
        z=todo.pop()
        y=[z[::-1]]
        y += [tuple(tuple(sorted((p[i],p[j]))) for i,j in z) for p in Q]
        y += [z[:i]+(z[i+1],z[i])+z[i+2:] for i in range(3) if not set(z[i])&set(z[i+1])]
        for v in y:
            if v not in seen:seen.add(v);todo.append(v)
    return seen


def small_base():
    bad={
      "12131424": ("AAAA", "-12:34 13:14 14:13 14:14 14:23", -4130859375),
      "12132414": ("AAAB", "12:23 -13:13 14:12 14:14 14:23", -4130859375),
      "12132434": ("AAAA", "-12:12 13:13 13:14 13:24 14:24", -2187500000),
      "12133424": ("AAAB", "-12:12 13:14 14:14 14:23 14:24", -2187500000),
      "12341324": ("AACD", "-12:23 13:12 13:13 13:34 14:12", -3076555218750),
    }
    angle=dict(A=(3,4,5), B=(4,3,5), C=(5,12,13), D=(12,5,13))
    for w,(v,form,expected) in bad.items():
        U=ident(4)
        for k,ch in enumerate(v):
            a,b=pair(w[2*k:2*k+2]); c,s,q=angle[ch]
            V=[[q*z for z in row] for row in ident(4)]
            V[a][a]=V[b][b]=c;V[a][b]=s;V[b][a]=-s
            U=matmul(V,U)
        F=[]
        for t in form.split():
            I,J=map(pair,t.lstrip('-').split(':'))
            F.append((I,J,-1 if t.startswith('-') else 1))
        require(all(sum(s for I,J,s in F if set(I)=={p[j] for j in J})>=0 for p in Q),
                "permutation polytope inequality")
        require(sum(s*det(U,I,J)**2 for I,J,s in F)==expected<0,"base gate separation")
    C4=tuple(map(pair,("12","13","24","34")))
    for w in permutations(C4):
        require(key(min(orbit(w))) in bad,"every order of C4")
    Tc=tuple(map(pair,("12","13","23","14")))
    for w in permutations(Tc):
        a,b,c,p=(w.index(e) for e in Tc)
        if min(a,b)<p<max(a,b):
            require(key(min(orbit(w))) in bad,"every interposed triangle pendant")
    print("PASS base four-gate obstructions")


def flip(blocks,bits,occupancy):
    Z=set(occupancy)
    for (u,v),b in zip(blocks,bits):
        if b and ((u in Z)!=(v in Z)):Z.symmetric_difference_update((u,v))
    return tuple(sorted(Z))


def layer(n,blocks,c,s):
    M=[[0]*n for _ in range(n)]
    for i,j in blocks:
        M[i][i]=M[j][j]=c
        M[i][j],M[j][i]=s,-s
    return M


def alternating_check(m,c=5,s=12,q=13):
    n=2*m
    A=[(2*i,2*i+1) for i in range(m)]
    B=[(2*i+1,(2*i+2)%n) for i in range(m)]
    U=matmul(layer(n,B,c,s),layer(n,A,c,s))
    Z=range(0,n,2)
    checks=0
    for u in product((0,1),repeat=n):
        J=flip(A,u[:m],Z); I=flip(B,u[m:],Z)
        h=sum(u)
        rhs=c**(2*(n-h))*s**(2*h)+c**(2*h)*s**(2*(n-h))+2*(-1)**(m-1+h)*(c*s)**n
        require(det(U,I,J)**2==rhs,"all-active complement interference")
        checks+=1
    for missing in combinations(range(n),2):
        z=[1]
        for i in range(n-1):
            vertex=(i//2) if i%2==0 else (m+i//2)
            z.append(z[-1] ^ int(vertex not in missing))
        require(z[0]^z[-1]==int(n-1 not in missing),"cyclic occupancy")
        Z=[i for i,x in enumerate(z) if x]
        k=len(Z)
        for a in product((0,1),repeat=n-2):
            vals=iter(a); u=tuple(0 if i in missing else next(vals) for i in range(n))
            J=flip(A,u[:m],Z); I=flip(B,u[m:],Z)
            p=F(c**(2*(n-2-sum(a)))*s**(2*sum(a)),q**(2*(n-2)))
            require(F(det(U,I,J)**2,q**(4*k))==p,"all two-omitted marginals")
            checks+=1
    x=F(s*s,c*c)
    require(-(1+x**-3)/3>(x**-2-1)/2,"Fourier positivity conflict")
    print("PASS alternating",n,checks)


if __name__=="__main__":
    small_base()
    for m in (3,4,5):
        alternating_check(m)
