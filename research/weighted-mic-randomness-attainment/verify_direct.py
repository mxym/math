#!/usr/bin/env python3
"""Directly assemble Hermitian effects, compute tomography rank and guessing."""
from cmath import exp
from math import pi,sqrt
from itertools import product
from random import Random


def outer(v):
    return [[a*b.conjugate() for b in v] for a in v]


def normalize(u):
    return [x/sum(u) for x in u]


def create(r,*,epsilon=None,phase=None,rotation=False):
    d=len(r)
    e=1/(2*d**4) if epsilon is None else epsilon
    theta=pi/(2*d) if phase is None else phase
    E=[]
    for a,b in product(range(d),repeat=2):
        z=[sqrt((1/d+e*((a==i)-r[a]))/d)*exp(1j*(b*i*2*pi/d+(a==i)*theta))
           for i in range(d)]
        if rotation and d>1:
            z[0],z[1]=(3*z[0]+4*z[1])/5,(-4*z[0]+3*z[1])/5
        E.append(outer(z))
    return E


def hermrow(H):
    d=len(H)
    out=[H[i][i].real for i in range(d)]
    for i in range(d):
        for j in range(i+1,d):
            out.extend((H[i][j].real,H[i][j].imag))
    return out


def elimination(M,tol=1e-10):
    M=[list(row) for row in M]
    h=len(M)
    ix=0
    mn=100.
    for col in range(len(M[0])):
        p=max(range(ix,h),key=lambda j:abs(M[j][col]))
        value=M[p][col]
        if abs(value)<tol:
            continue
        mn=min(mn,abs(value))
        M[p],M[ix]=M[ix],M[p]
        for j in range(ix+1,h):
            f=M[j][col]/value
            for k in range(col+1,len(M[0])):
                M[j][k]-=f*M[ix][k]
        ix+=1
        if ix==h:
            break
    return ix,mn


def traceprod(U,V):
    return sum(a*b for i,row in enumerate(U) for a,b in zip(row,(r[i] for r in V)))


def density(r,rotation=False):
    d=len(r)
    R=[[0.]*d for _ in r]
    for i,x in enumerate(r):
        R[i][i]=x
    if rotation and d>1:
        x,y=r[:2]
        R[0][0]=(9*x+16*y)/25
        R[1][1]=(16*x+9*y)/25
        R[0][1]=R[1][0]=12*(y-x)/25
    return R


def norms(r,rotation=False):
    E=create(r,rotation=rotation)
    d=len(r)
    assert len(E)==d*d
    assert all(abs(sum(H[i][j] for H in E)-(i==j))<1e-12
               for i,j in product(range(d),repeat=2))
    R=density(r,rotation)
    for M in E:
        assert abs(traceprod(R,M)-1/d**2)<1e-12
        assert all(abs(M[i][i]*M[j][j]-abs(M[i][j])**2)<1e-12
                   for i,j in product(range(d),repeat=2))
    n,p=elimination(list(map(hermrow,E)))
    assert n==d*d and p>1e-9
    return E


def guessing(U):
    q=normalize([u*u for u in U])
    s=[sqrt(a) for a in q]
    d=len(q)
    E=norms(normalize(s))
    p=0.
    c=sum(s)/d**2
    for H in E:
        # Canonical purification blocks sigma_x and support-PGM effects.
        sig=[[s[i]*H[j][i]*s[j] for j in range(d)] for i in range(d)]
        G=[[H[j][i]*(q[i]>0)*(q[j]>0) for j in range(d)] for i in range(d)]
        p+=traceprod(sig,G).real
        bound=[[sig[i][j]/sqrt(s[i]*s[j]) if s[i]*s[j]>0 else 0.
                  for j in range(d)] for i in range(d)]
        assert abs(sum(bound[i][i] for i in range(d))-c)<1e-12
        assert abs(sum(abs(x)**2 for row in bound for x in row)-c*c)<1e-12
    assert abs(p-d*d*c*c)<1e-12
    return len(E)


def main():
    d0=0
    rng=Random(241016447)
    for d in range(1,10):
        for r in ([1/d]*d,[1.]+[0.]*(d-1),
                  normalize([i+1 for i in range(d)]),
                  normalize([rng.randrange(1,100) for i in range(d)])):
            norms(r,rotation=True)
            d0+=1
    # A zero perturbation has identical diagonal rows; a real phase
    # makes opposite sites of the even half-shift band coincide.
    for d in (2,4,6,8):
        r=normalize(list(range(1,d+1)))
        assert elimination(list(map(hermrow,create(r,epsilon=0.))))[0]<d*d
        assert elimination(list(map(hermrow,create(r,phase=0.))))[0]<d*d
    gs=sum(guessing(u) for u in ([1],[1,0],[1,3],[3,0,1,2],
                                [2,2,2,2,2],[1,0,0,2,3,1,5,0]))
    print(f"direct checks: {d0} complete real-Hermitian tomography ranks (d=1..9), rotated-state normalization PASS")
    print(f"direct checks: {gs} purification/PGM effects, 8 rank-loss controls PASS")


if __name__=='__main__':
    main()
