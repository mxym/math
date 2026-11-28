#!/usr/bin/env python3
"""Exact rational controls for the five-axis boundary theorem (standard library)."""
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
def weights(Y):
    return lin([[1]*5]+[[phase(y,k)[j] for y in Y] for k in (2,4) for j in (0,1)],[1,0,0,0,0])
def energy_matrix(Y,j,t):
    r=(1-t*t)/(1+t*t);h=2*t/(1+t*t)
    def dot3(i,k):
        c=dot(Y[i],Y[k])
        return c if (i==j)==(k==j) else r*c
    G=[[dot3(i,k) for k in range(5)]for i in range(5)]
    assert all(G[i][k]<=F(1,2) for i in range(5) for k in range(i))
    return [[v**4-v*v/4 for v in row] for row in G],h
def optimum(A):
    # Exact active-set optimality: PSD by positive pivots, then a single KKT
    # witness with all outsider potentials >= its own energy is conclusive.
    M=[r[:] for r in A]
    for k in range(len(M)):
        assert M[k][k]>0
        for i in range(k+1,len(M)):
            for j in range(k+1,len(M)):M[i][j]-=M[i][k]*M[k][j]/M[k][k]
    for n in range(1,6):
        for S in combinations(range(5),n):
            p=lin([[A[i][j] for j in S]for i in S],[1]*n);e=1/sum(p);p=[v*e for v in p]
            if min(p)<0:continue
            if all(sum(A[i][j]*q for j,q in zip(S,p))>=e for i in range(5)):return e
    raise AssertionError('no positive definite QP witness')
def main():
    step=F(1,2),F(1,2);B=[phase(step,i)for i in range(6)]
    count=0;signs=0
    for s,t in [('1/16','1/11'),('1/10','1/10'),('1/8','1/7')]:
        Y=B[:3]+[mul(B[3],rot(s)),mul(B[4],rot(t))]
        assert weights(Y)==[F(1,3)]*3+[0,0]
        for j in [3,4]:
            for denom in [24,48,96,192,384]:
                A,h=energy_matrix(Y,j,F(1,denom));cost=optimum(A)
                ratio=(F(1,4)-cost)/h**4
                assert F(1,8)<=ratio<100
                count+=1
    # Positive corrected active gaps, but final inactive pair now shorter than
    # 60 degrees. Repair that gap twice moving only the node being tested.
    for d in [100,200,300,500]:
        v=rot(F(1,d));L1=mul(B[1],v);L2=mul(mul(B[2],v),v)
        s=rot(F(1,10));t=rot(F(1,10)-F(1,3*d))
        Y=[B[0],L1,L2,mul(B[3],s),mul(B[4],t)]
        assert dot(Y[3],Y[4])>F(1,2)
        w=weights(Y);assert min(w)>0
        for j,u in [(3,mul(B[3],t)),(4,mul(B[4],s))]:
            Z=Y[:];Z[j]=u
            assert all(dot(Z[i],Z[k])<=F(1,2) for i in range(5)for k in range(i))
            assert weights(Z)[j]*w[j]>0;signs+=1
    print('PASS:',count,'exact optimized nonplanar lifts;',signs,'one-node sign repairs')
if __name__=='__main__':main()
