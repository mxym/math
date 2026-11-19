"""Independent direct cofactor, planted PGF and collision checks. No dependencies."""
from fractions import Fraction as F
from itertools import product
from collections import Counter
from math import comb,prod
def check(a,b,tag):
    if a!=b:raise ArithmeticError((tag,a,b))
def det(A):
    A=[r.copy() for r in A];n=len(A);den=sign=1
    for c in range(n-1):
        if not A[c][c]:
            p=next((i for i in range(c+1,n) if A[i][c]),None)
            if p is None:return 0
            A[p],A[c]=A[c],A[p];sign=-sign
        pivot=A[c][c]
        for i in range(c+1,n):
            for j in range(c+1,n):
                num=A[i][j]*pivot-A[i][c]*A[c][j]
                if num%den:raise ValueError('inexact Bareiss')
                A[i][j]=num//den
        den=pivot
    return sign*A[-1][-1]
def count(A,B,x):
    n=len(x);lap=[[0]*n for _ in range(n)]
    for u in range(n):
        for v in range(u):
            if (u in A and v in A) or (u in B and v in B):continue
            w=x[u]*x[v];lap[u][u]+=w;lap[v][v]+=w;lap[u][v]-=w;lap[v][u]-=w
    return det([r[:-1] for r in lap[:-1]])
def formulas():
    n2=ng=nm=0
    for n in range(2,25):
        for k in range(1,n):
            m=n-k;A=set(range(k));mu=F(comb(n-2,2),n)
            for j in range(max(0,2*k-n),k+1):
                B=set(range(j))|set(range(k,2*k-j))
                exact=F(count(A,B,[1]*n),n**(n-2));q=k-j;o=n-2*k+j
                predicted=F(o,n)**j*F(m,n)**(2*(q-1))*F(n-j,n)
                check(exact,predicted,('overlap',n,k,j));n2+=1
            for x in [[1]*n,[1+(4*i+3)%11 for i in range(n)],[2+(i*i+2)%5 for i in range(n)]]:
                check(count(A,A,x),prod(x)*sum(x)**(m-1)*sum(x[k:])**(k-1),('weighted',n,k));ng+=1
            if n<=7:
                U=m-1;R=k-1;D=Counter()
                for w in product(*([range(n)]*U+[range(k,n)]*R)):
                    D[sum(comb(t,2) for t in Counter(w).values())]+=1
                total=sum(D.values());EW=sum(F(d*cnt,total) for d,cnt in D.items())
                var=sum(F(cnt,total)*(d-EW)**2 for d,cnt in D.items())
                check(EW,mu+F(comb(R,2)*k,n*m),('mean',n,k))
                Nrr=comb(R,2);Nother=comb(n-2,2)-Nrr
                check(var,F(Nother*(n-1),n*n)+F(Nrr*(m-1),m*m)+F(U*R*(R-1)*k,n*n*m),('cov',n,k))
                nm+=1
    print('Direct integer cofactors vs overlap formula:',n2,'cases, n=2..24 (including empty classes)')
    print('Weighted split-graph cofactors vs planted degree pgf:',ng,'positive integer evaluations')
    print('Planted draw occupancy mean and variance:',nm,'exact distributions through n=7')
def pathrat():
    t=0
    for n in range(2,161):
        for k in range(1,(n+1)//2+1):
            check(F(comb(n,k),comb(n-k+1,k))*F(n-k,n)**(k-1),prod(1+F(k*j,n*(n-k-j)) for j in range(k-1)),('path',n,k));t+=1
    print('Path-normalized exact expectation identity:',t,'cases, n=2..160')
if __name__=='__main__':formulas();pathrat();print('PASS')
