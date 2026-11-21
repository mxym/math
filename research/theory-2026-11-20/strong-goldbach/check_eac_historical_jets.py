#!/usr/bin/env python3
"""Rebuild genuine components and rational Puiseux obstructions; standard Python."""
from fractions import Fraction as F
from functools import lru_cache
from math import gcd,lcm

def check(b,msg):
    if not b:raise ValueError(msg)

@lru_cache(None)
def factors(n):
    out={};d=2
    while d*d<=n:
        while n%d==0:n//=d;out[d]=out.get(d,0)+1
        d=3 if d==2 else d+2
    if n>1:out[n]=out.get(n,0)+1
    return out

def eac(N):
    V=[v for v in range(2,N-1) if factors(v)=={v:1}]
    graph={p:tuple(factors(N-p)) for p in V}
    back={p:[] for p in V}
    for p,ns in graph.items():
        for n in ns:back[n].append(p)
    def visit(start,G):
        seen={start};stk=[start]
        while stk:
            for n in G[stk.pop()]:
                if n not in seen:seen.add(n);stk.append(n)
        return seen
    available=set(V); eacs=[]
    while available:
        p=min(available);fwd=visit(p,graph);group=fwd&visit(p,back);available-=group
        if len(group)>1 and group==fwd and all(N-v not in group for v in group):eacs.append(sorted(group))
    check(len(eacs)==1,'unique historical EAC');C=eacs[0]
    return C,[[factors(N-p).get(q,0) for q in C] for p in C]

def invert(A):
    n=len(A); E=[[F(x) for x in r]+[F(int(j==i)) for j in range(n)] for i,r in enumerate(A)]
    for j in range(n):
        k=next(i for i in range(j,n) if E[i][j]);E[j],E[k]=E[k],E[j]
        z=E[j][j];E[j]=[v/z for v in E[j]]
        for i in range(n):
            if i!=j and E[i][j]:
                z=E[i][j];E[i]=[x-z*y for x,y in zip(E[i],E[j])]
    return [r[n:] for r in E]

# certificate = (integer polynomial monomials, first positive power of s, signed coefficient).
cases={
128: ([(1,(11,)),(-1,(3,3)),(-1,(3,))],1,-1),
1718: ([(3,(5,)),(-3,(3,)),(-4,())],2,F(14,3)),
1862: ([(2,(5,)),(-2,(3,)),(-3,())],1,F(11,4)),
1928: ([(1,(5,)),(-1,(3,3)),(2,(3,)),(-1,())],2,4),
6142: ([(2,(7,17)),(-4,(3,3,13)),(-2,(5,13)),(2,(3,3,7)),(2,(5,5,5)),(-4,(3,)),(-1,(5,17)),(1,(3,3,3,3))],4,2)
}

def mul(a,b,J):
    return [sum(a[i]*b[h-i] for i in range(h+1)) for h in range(J+1)]

def run(N,cert):
    pol,ell,c=cert;C,A=eac(N);n=len(C); B=invert(A);w=[sum(r) for r in B]
    D=lcm(*(z.denominator for z in w)); d=[int(D*z) for z in w]
    check(all(0<x<D for x in d),'interior weights')
    ii={p:i for i,p in enumerate(C)}
    P=[(a,tuple(ii[p] for p in v)) for a,v in pol]; weights=[sum(d[i] for i in v) for _,v in P]
    H=max(weights); J=H+ell; Y=[[F(1)] for i in C]; logY=[[] for i in C];logZ=[[] for i in C]
    for h in range(1,J+1):
        for j in range(n):
            dz=D-d[j]
            raw=-Y[j][h-dz] if h>=dz else 0
            corr=sum(l*logZ[j][l-1]*(-Y[j][h-l-dz]) for l in range(1,h) if h-l>=dz)
            logZ[j].append(F(raw)-F(corr,h))
        for i in range(n):
            ly=sum(B[i][j]*logZ[j][-1] for j in range(n))
            logY[i].append(ly); Y[i].append(sum(l*logY[i][l-1]*Y[i][h-l] for l in range(1,h+1))/h)
    one=[F(1)]+[F(0)]*J
    # Independent check of each original equation by literal polynomial multiplication, no logs.
    for i,row in enumerate(A):
        v=one[:]
        for j,a in enumerate(row):
            for _ in range(a):v=mul(v,Y[j],J)
        z=one[:]; dz=D-d[i]
        for j in range(J+1-dz):z[j+dz]-=Y[i][j]
        check(z==v,'literal scaled defining equation')
    out=[F(0)]*(J+1)
    for (a,v),wt in zip(P,weights):
        u=one[:]
        for i in v:u=mul(u,Y[i],J)
        delta=H-wt
        for h in range(J+1-delta):out[delta+h]+=a*u[h]
    check(not any(out[:-1]) and out[-1]==c,'signed first nonzero term')
    C0=sum(abs(a)*3**len(v) for a,v in P);S=max(sum(abs(x) for x in r) for r in B)
    R=F(1,16)/(1+S); ceilS=-((-S.numerator)//S.denominator)
    s0=min(R/2, R*F(2,3)**ceilS,abs(c)*R**(J+1)/(4*C0),F(1,4)/(1+abs(c)))
    # A computable decimal order of magnitude of the crude upper bound s0^-D, without logs.
    bound=(1/s0)**D; digits=len(str(bound.numerator//bound.denominator))
    print('N signature',N,'size',n,'D',D,'H',H,'jet',c,'s^',ell,'height upper bound < 10^',digits)

for N,cert in cases.items():run(N,cert)
C,A=eac(2200);check(C==[3,13] and A==[[0,3],[7,0]],'two-label control')
print('2200 pure cycle: 3,7 exponents; PASS')
