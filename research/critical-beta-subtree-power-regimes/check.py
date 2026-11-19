"""Exact finite cross-checks. There is no simulation; no asymptotic law is tested as a finite identity."""
from fractions import Fraction as F
from functools import lru_cache
from collections import defaultdict
from math import comb, factorial

def ck(v):
    if not v:raise ArithmeticError("exact identity failed")
@lru_cache(None)
def H(j): return sum((F(1,i) for i in range(1,j+1)),F(0))
def q(m,i): return F(m,2*i*(m-i))/H(m-1)
@lru_cache(None)
def trees(n):
    if n==1:return {():F(1)}
    return {(u,v):w*z*q(n,i) for i in range(1,n) for u,w in trees(i).items() for v,z in trees(n-i).items()}
@lru_cache(None)
def sizes(t):
    if not t:return (1,())
    (i,I),(j,J)=map(sizes,t); return i+j,(i+j,)+I+J
@lru_cache(None)
def visit(n,m):
    if n<=m:return F(n==m)
    return sum(visit(i,m)/((n-i)*H(n-1)) for i in range(m,n))
@lru_cache(None)
def pot(n,p):
    if n==1:return F(0),F(0)
    m=F(0);s=F(0);c=F(n)**p
    for i in range(1,n):
        a,u=pot(i,p);b,v=pot(n-i,p);d=q(n,i)
        m+=d*(a+b+c);s+=d*(u+v+2*a*b+2*c*(a+b)+c*c)
    return m,s
def test():
    powers=(-2,-1,0,1,2,3,4);N=0;M=0
    for n in range(1,10):
        L=trees(n);ck(sum(L.values())==1);N+=len(L)
        for p in powers:
            f=g=F(0)
            for t,P in L.items():
                _,a=sizes(t);u=sum(F(i)**p for i in a);f+=P*u;g+=P*u*u
            ck((f,g)==pot(n,p))
            ck(f==n*sum(visit(n,i)*F(i)**(p-1) for i in range(2,n+1)))
            M+=1
    print("Ordered trees",N,"finite integer-power cases",M,"both moments and occupation means PASS")
    # Two disjoint labelled k-sets in the sampled 2k-label tree: directly enumerate
    # all ordered root split masks, root time plus residual clocks for unbroken groups.
    for k in range(2,8):
        n=2*k;mask=(1<<n)-1;A=(1<<k)-1;B=mask^A;u=H(n-1);v=H(k-1);surv=F(); both=F()
        for side in range(1,mask):
            i=side.bit_count();m=q(n,i)/comb(n,i);a=(A&side in (0,A));b=(B&side in (0,B))
            surv+=m*(int(a)+int(b));both+=m*int(a and b)
        raw=2/u**2+surv/(u*v)+both/v**2
        # Beta(k,k) is the binary cross coefficient in Bertoin's second-moment recursion.
        beta=F(factorial(k-1)**2, factorial(2*k-1))
        ck(raw==(2/v+beta/v**2)/u);var=raw-1/v**2;ck(var>0)
        if k==2:ck(var==F(2,11))
        print("disjoint",k,"-label sets: continuum covariance",var)
if __name__=='__main__':test()
