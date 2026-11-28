#!/usr/bin/env python3
"""Exact rational controls for the uniform near-planar five-point theorem (standard library)."""
from fractions import Fraction as F
from itertools import combinations

# (a,b) means a+i*b*sqrt(3). Rotations, dot products, and f remain rational.
def rot(t):
    t=F(t)
    return (1-3*t*t)/(1+3*t*t),2*t/(1+3*t*t)
def mul(x,y):return x[0]*y[0]-3*x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def dot(x,y):return x[0]*y[0]+3*x[1]*y[1]
def phase(x,k):
    y=(F(1),F(0))
    for _ in range(k):y=mul(x,y)
    return y
def lin(M,b):
    n=len(b);T=[list(map(F,a))+[F(z)] for a,z in zip(M,b)]
    for j in range(n):
        i=next(i for i in range(j,n) if T[i][j]);T[i],T[j]=T[j],T[i]
        v=T[j][j];T[j]=[q/v for q in T[j]]
        for i in range(n):
            if i!=j:
                v=T[i][j];T[i]=[q-v*r for q,r in zip(T[i],T[j])]
    return [a[-1] for a in T]
def optimum(A):
    # Exact active-set optimality: PSD by positive pivots, then a single KKT
    # witness with all outsider potentials >= its own energy is conclusive.
    M=[r[:] for r in A]
    for k in range(len(M)):
        assert M[k][k]>0
        for i in range(k+1,len(M)):
            for j in range(k+1,len(M)):M[i][j]-=M[i][k]*M[k][j]/M[k][k]
    for n in range(1,len(M)+1):
        for S in combinations(range(len(M)),n):
            p=lin([[A[i][j] for j in S]for i in S],[1]*n);e=1/sum(p);p=[v*e for v in p]
            if min(p)<0:continue
            if all(sum(A[i][j]*q for j,q in zip(S,p))>=e for i in range(len(M))):return e
    raise AssertionError('no positive definite QP witness')
def main():
    step=F(1,2),F(1,2);B=[phase(step,i)for i in range(6)]
    n=pooled=0
    for t0 in [F(0),F(1,13),F(1,5)]:
        orig=B[:4]+[mul(B[4],rot(t0))]
        assert all(dot(orig[i],orig[j])<=F(1,2) for i in range(5) for j in range(i))
        # The base measure is positive on every end of the three regular axes.
        p=list(map(F,['1/6','1/3','1/3','1/6','0'])) if t0 else list(map(F,['1/6','1/6','1/3','1/6','1/6']))
        assert all(sum(p[i]*phase(orig[i],k)[j] for i in range(5))==0 for k in (2,4) for j in (0,1))
        for ang in [0,F(1,5000)]:
            v=rot(ang)
            Y=[mul(y,phase(v,i))if (not t0 or i<4) else y for i,y in enumerate(orig)]
            for den in [80,160,320]:
                for vector in [(1,1,1,1,1),(1,2,3,4,1),(1,0,0,0,2),(0,0,0,0,1)]:
                    # Give distinct points mutually orthogonal normal directions;
                    # endpoint-only lifts include exactly coincident projective axes.
                    ts=[F(k,den) for k in vector]
                    r=[(1-t*t)/(1+t*t)for t in ts];h=[2*t/(1+t*t)for t in ts]
                    G=[[F(1) if i==j else r[i]*r[j]*dot(Y[i],Y[j])for j in range(5)]for i in range(5)]
                    assert all(G[i][j]<=F(1,2) for i in range(5) for j in range(i))
                    A=[[u**4-u*u/4 for u in row]for row in G]
                    I=[]
                    for i in range(5):
                        if not any(A[i]==A[j] for j in I):I.append(i)
                    pooled+=int(len(I)<5)
                    cost=optimum([[A[i][j] for j in I]for i in I])
                    normal_trace=sum(u*u for u in h)
                    assert 0<normal_trace and cost <= F(1,4)-normal_trace**2/200
                    n+=1
    print('PASS:',n,'exact KKT certificates, including',pooled,'pooled-axis cases')
if __name__=='__main__':main()
