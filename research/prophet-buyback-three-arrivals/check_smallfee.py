#!/usr/bin/env python3
"""Exact finite check of the quadratic-mesh unrestricted-horizon examples."""
from fractions import Fraction as Q
from itertools import product

def require(test):
    if not test:
        raise ArithmeticError("small-fee check failed")

def main():
    total=0; enum=0
    for n in range(2,86):
        f=Q(1,n*n-1); c=f/(1+f)
        x=[Q((n+1)*i,n*(i+1)) for i in range(n+1)]
        p=[Q(0)]+[Q(2*i-1,i*i) for i in range(1,n+1)]
        k=[Q(i*i,n*n) for i in range(n+1)]
        H=sum(Q(1,i) for i in range(1,n+1))
        O=1-(n-H)/(n*(n-1)); M=(n+1)*(n*n-2*n-3+3*(H+Q(1,n+1)))/n**3
        # Backward induction including possibility of a fee-paying switch to zero.
        v=x.copy()
        for i in range(n,0,-1):
            z=v[0]
            last=v[i]
            for j in range(i):
                q=p[i]; held=x[j]
                v[j]=(1-q)*max(v[j],z-f*held)+q*max(v[j],last-f*held)
            require(x[i-1]==(1-c/k[i])*x[i])
            total+=1
        require(v[0]==O)
        require(sum(x[i]*(k[i]-k[i-1]) for i in range(1,n+1))==M)
        require((M-O)/f==2*H-4+(2*H+1)/n-(3*H-5)/n**2-3*H/n**3)
        if n<=10:
            ert=Q()
            for bits in product((False,True),repeat=n-1):
                prob=Q(1); mx=x[1]
                for j,b in enumerate(bits,2):
                    prob*=p[j] if b else 1-p[j]
                    if b: mx=x[j]
                ert+=prob*mx;enum+=1
            require(ert==M)
    print('PASS: exact backward-induction horizons 2..85; stage identities =',total)
    print('PASS: direct offline outcome vectors through horizon 10 =',enum)
if __name__=='__main__': main()
