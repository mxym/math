#!/usr/bin/env python3
"""Exact finite controls for the rotating-grid proof. Standard Python, no floating point."""
from fractions import Fraction as F
from itertools import combinations
from math import comb

def partitions_slack(parts,total):
    # Weak compositions via separators, including asymmetric and boundary profiles.
    for c in combinations(range(total+parts-1),parts-1):
        a=(-1,)+c+(total+parts-1,)
        yield tuple(a[j+1]-a[j]-1 for j in range(parts))
def circnorm(theta,P):
    a=theta%P
    return min(a,P-a)
def profile(m,slack):
    n=2*m+1;B=sum(slack);P=2*(n+1)*B
    assert B>0
    for i in range(n):
        seq=slack[i:]+slack[:i];t=[0]
        for a in seq[:-1]:t.append(t[-1]+2*(B+a))
        for h,r in ((1,0),(2,m)):
            Y=[(h*z)%P for z in t]
            if len(set(Y))<n:
                assert h==2
                assert any(all((v+b*4*B)%P in set(Y) for b in range(m+1)) for v in Y)
                continue
            # Per theorem: grid phase is the midpoint of the r-th slack gap.
            beta=sum(seq[:r])*2+seq[r]
            g=(beta-2*B if h==1 else 2*beta)%P
            grid=[(g+4*B*b)%P for b in range(m+1)]
            def sign_change(q):
                if q in Y[1:]:return 0
                # sign of the cardinal value is parity of roots on the arc from Y[0]=0.
                return -1 if sum(0<z<q for z in Y[1:])%2 else 1
            signs=[sign_change(x) for x in grid]
            assert all(z>=0 for z in signs)
            if min(seq):
                assert signs==[1]*(m+1)
                assert all(circnorm(y-x,P)>=h*min(seq) for y in Y[1:] for x in grid)
            if not any(signs):
                assert set(grid)<=set(Y[1:])
def gauss_jordan(A,b):
    M=[list(row)+[rhs] for row,rhs in zip(A,b)];n=len(M)
    for j in range(n):
        k=next(i for i in range(j,n) if M[i][j]);M[k],M[j]=M[j],M[k]
        v=M[j][j];M[j]=[a/v for a in M[j]]
        for i in range(n):
            if i!=j:
                z=M[i][j];M[i]=[a-z*b for a,b in zip(M[i],M[j])]
    return [row[-1] for row in M]
def zpow(z,k):
    x,y=map(F,z);a,b=F(1),F(0)
    for _ in range(k):a,b=a*x-b*y,a*y+b*x
    return a,b
def qweights(nodes,m,h):
    A=[[F(1)]*len(nodes)]
    for k in range(1,m+1):
        vals=list(zip(*(zpow(z,h*k) for z in nodes)));A.extend(vals)
    b=[F(1)]+[F(0)]*(2*m);w=gauss_jordan(A,b)
    assert all(sum(x*y for x,y in zip(row,w))==z for row,z in zip(A,b))
    return w
def point(t):return ((1-t*t)/(1+t*t),2*t/(1+t*t))
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def main():
    counts=[]
    for m in range(1,7):
        n=2*m+1;k=0
        # Both weak and strictly positive gaps, checked at every node.
        for budget in [2,3]:
            for row in partitions_slack(n,budget):
                for seq in [row,tuple(1+z for z in row)]:
                    profile(m,seq);k+=1
        counts.append(k)
    print('exact cyclic gap profiles, m=1..6:',counts)
    for m,params in [(1,[F(0),F(2),F(-2)]),(2,[F(0),F(3,4),F(3),F(-3),F(-3,4)]),(2,[F(0),F(7,10),F(31,10),F(-29,10),F(-3,4)])]:
        X=list(map(point,params));threshold=[None,F(0),F(1,2)][m]
        assert all(dot(x,y)<threshold for x,y in combinations(X,2))
        for h in [1,2]:
            w=qweights(X,m,h);assert min(w)>0
            if m==2 and h==2:
                def f(z):return z**4-z*z/4
                assert sum(wi*wj*f(dot(x,y)) for wi,x in zip(w,X) for wj,y in zip(w,X))==F(1,4)
            print('circle control',m,h,'weights',*[str(z) for z in w])
    print('PASS')
if __name__=='__main__':main()
