#!/usr/bin/env python3
"""Exact inverse-Fourier verification; no packages, floating arithmetic or asserts."""
from fractions import Fraction
from math import gcd, prod
from collections import Counter

def check(x):
    if not x: raise ValueError("certificate mismatch")

def fac(n):
    ans={}; p=2
    while p*p<=n:
        while n%p==0:
            ans[p]=ans.get(p,0)+1; n//=p
        p+=1
    if n>1: ans[n]=1
    return ans

def v(x,p,e):
    j=0
    while j<e and x%p==0:
        x//=p; j+=1
    return j

def factors(n):
    return [j for j in range(1,n+1) if n%j==0]

def mu(n):
    d=fac(n)
    return 0 if max(d.values(),default=0)>1 else (-1)**len(d)

def phi(n):
    return prod((p-1)*p**(e-1) for p,e in fac(n).items())

def local(p,e,u,j):
    if u==e: return 1
    if u==0 and j==0: return Fraction(p-2,p-1)
    if j<=u: return 1
    if j==u+1: return Fraction(-1,p-1)
    return 0

def verify(n):
    G=[x for x in range(n) if gcd(x,n)==1]
    D=factors(n); F=fac(n); h=len(G)
    # sum_{primitive chars mod f} chi(-t), by primitive orthogonality
    S={(f,t):sum(mu(f//d)*phi(d) for d in factors(f) if (t+1)%d==0)
       for f in D for t in G}
    ker=[Counter() for dlt in range(n)]
    # ordered unit pairs determine the raw multiplicative difference kernel.
    for b in G:
        inv=pow(b,-1,n)
        for a in G:
            ker[(a+b)%n][a*inv%n]+=1
    checked=0
    for dlt in range(n):
        lam={f:prod(local(p,e,v(dlt,p,e),v(f,p,e)) for p,e in F.items()) for f in D}
        for f in D:
            if S[f,n-1]>0 and dlt%2==0:
                check(bool(lam[f])==(dlt%(f//prod(fac(f)))==0))
        for t in G:
            # Fourier inversion on G contributes 1/h, cancelling the h
            # in the predicted J. The above S supplies the -1 phase.
            check(sum(lam[f]*S[f,t] for f in D)==ker[dlt][t])
            checked+=1
    # Complementary windows of genuine prime units, with variable weights.
    U=[x for x in range(2,n) if phi(x)==x-1 and gcd(x,n)==1]
    window=0
    for f in D:
        rad=prod(fac(f)); sep=f//rad
        for center in {n//2,n//3,2*n//5}:
            A={x:1+x%5 for x in U if 3*abs(x-center)<sep}
            B={y:1+y%7 for y in U if 3*abs(y-(n-center))<sep}
            target=sum(w*B.get(n-x,0) for x,w in A.items())
            # Direct primitive trace uses -x/y rather than x+y congruence.
            L=sum(w*z*S[f,x*pow(y,-1,n)%n] for x,w in A.items() for y,z in B.items())
            check(L==S[f,n-1]*target); window+=1
    if n>=8 and n&(n-1)==0:
        h2=n//2
        check(all((h2-x)%n==(h2-1)*x%n for x in G))
        check(all(ker[h2][t]==(h if t==h2-1 else 0) for t in G))
        check(all((local(2,fac(n)[2],fac(n)[2]-1,v(f,2,fac(n)[2]))==
                   (-1 if f==n else 1)) for f in D))
    return checked,window

def main():
    ns=sorted(set(range(4,101,2))|{108,120,126,128,144,150,162,180,192,210,216,256})
    R=[verify(n) for n in ns]
    print("PASS",len(ns),"even moduli;",sum(x for x,y in R),"histogram values;",
          sum(y for x,y in R),"genuine-prime window/conductor tests")

if __name__=="__main__": main()
