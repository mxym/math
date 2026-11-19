from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import comb,prod

def check(ok):
    if not ok:
        raise RuntimeError("exact matched-tail inequality failed")

def bernoulli_sum(probs):
    n=len(probs)
    values=[F(0) for _ in range(n+1)]
    for mask in range(1<<n):
        values[mask.bit_count()]+=prod((p if (mask>>j)&1 else 1-p) for j,p in enumerate(probs))
    return values

def binom(n,p):
    return [comb(n,j)*p**j*(1-p)**(n-j) for j in range(n+1)]

def bracket(n,k,phi):
    a,b=F(0), F(1)
    for _ in range(19):
        c=(a+b)/2
        if sum(binom(n,c)[k:])<=phi:
            a=c
        else:
            b=c
    return a,b

grid=[F(j,4) for j in range(5)]
t=0
for n in range(1,6):
    for p in combinations_with_replacement(grid,n):
        d=bernoulli_sum(p)
        for k in range(1,n+1):
            phi=sum(d[k:])
            if phi in (0,1):
                continue
            lo,hi=bracket(n,k,phi)
            qlo,qhi=binom(n,lo),binom(n,hi)
            for j in range(k-1):
                check(sum(d[:j+1])<=sum(qlo[:j+1]))
            for j in range(k,n):
                check(sum(d[j+1:])<=sum(qhi[j+1:]))
            u=lambda q:sum(min(k,j)*x for j,x in enumerate(q))
            a=lambda q:sum(min(F(1),F(k,j+1))*x for j,x in enumerate(q))
            check(u(d)>=u(qlo) and a(d)>=a(qhi))
            t+=1
print(f"{t} exact finite marginal vectors/cuts; independently enumerated all assignments and bracketed binomial calibration; PASS")
