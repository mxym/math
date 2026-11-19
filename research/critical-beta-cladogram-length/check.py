"""Exact finite sanity checks for the drawn cladogram; standard library, Python 3."""
from fractions import Fraction as Q
from functools import lru_cache
from collections import defaultdict, Counter
from math import comb

def ck(x):
    if not x: raise ArithmeticError("exact check failed")
@lru_cache(None)
def H(n): return sum((Q(1,i) for i in range(1,n+1)), Q())
def q(n,i): return Q(n,2*i*(n-i))/H(n-1)
@lru_cache(None)
def law(n):
    if n==1: return {():Q(1)}
    return {(a,b):q(n,i)*p*r for i in range(1,n) for a,p in law(i).items() for b,r in law(n-i).items()}
@lru_cache(None)
def info(t):
    if not t:return (1,0,0,(),(),())
    A,B=map(info,t); n=A[0]+B[0]; h=1+max(A[1],B[1])
    d=A[2]+B[2]+2+abs(A[1]-B[1])
    w=tuple(sum(int(C[1]<=j<h)+(C[3][j] if j<len(C[3]) else 0) for C in (A,B)) for j in range(h))
    heights=(h,)+A[4]+B[4]; sizes=(n,)+A[5]+B[5]
    ck(d==sum(w)==h+sum(heights))
    ck(all(w[j]==1+sum(x>j for x in heights) for j in range(h)))
    return n,h,d,w,heights,sizes
@lru_cache(None)
def hit(n,m):
    if n<=m:return Q(n==m)
    return sum(hit(j,m)/(H(n-1)*(n-j)) for j in range(m,n))
@lru_cache(None)
def heightcdf(n,k):
    if k<0:return Q(0)
    if n==1:return Q(1)
    return sum(q(n,i)*heightcdf(i,k-1)*heightcdf(n-i,k-1) for i in range(1,n))
def main():
    sums=Counter(); last=None
    for n in range(1,11):
        T=law(n); ck(len(T)==comb(2*n-2,n-1)//n and sum(T.values())==1)
        sums["trees"]+=len(T)
        Ewidth=defaultdict(Q); eclade=defaultdict(Q); D=Q(0)
        for t,p in T.items():
            s,h,d,w,heights,sizes=info(t); ck(s==n)
            D+=p*d
            for j,wj in enumerate(w): Ewidth[j]+=wj*p
            for m,count in Counter(sizes).items(): eclade[m]+=count*p
        for m in range(2,n+1):
            ck(Q(n,m)*hit(n,m)==eclade[m]); sums["tagged-count identities"]+=1
        for j in range(n):
            root=1-heightcdf(n,j)
            rhs=root+sum(Q(n,m)*hit(n,m)*(1-heightcdf(m,j)) for m in range(2,n+1))
            ck(Ewidth[j]==rhs); sums["expected widths"]+=1
        ck(D==sum(Ewidth.values()) and D>=2*n-2)
        last=D
    print("PASS",dict(sums))
    print("E D(T_10) =",last)
if __name__=="__main__":main()
