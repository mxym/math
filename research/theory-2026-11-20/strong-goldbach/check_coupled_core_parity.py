"""Exact divisor-sign and interface checks for CoupledShortCoreParitySplit.md."""
from fractions import Fraction as F
from itertools import combinations

def f(s): return F(str(s))
def require(v, desc):
    if not v: raise RuntimeError(desc)

D,short,U=f(".219"),f(".22"),f(".50")
def left_data(xs):
    return sorted(sum(S,F(0)) for k in range(len(xs)+1)
                  for S in combinations(xs,k) if sum(S,F(0))<=short)
def sign(xs):
    return sum(((-1)**k*(1-ts) for k in range(len(xs)+1)
                for S in combinations(xs,k) if D<(ts:=sum(S,F(0)))<U), F(0))
checks=0
for P in range(3151,3170,2):
    for A in range(981,1000,2):
        for B in range(1001,1020,2):
            p,a,b=map(lambda v:F(v,10000),(P,A,B))
            v=1-p-a-b
            data=sorted([F(0),a,b,a+b])
            require(left_data((a,b,v))==data,"prime exact low data")
            require(sign((a,b,v))==-(p+a+b),"prime negative")
            for l in range(2301,2550,7):
                j=F(l,10000)
                k=v-j
                if f(".23")<k<f(".255") and j!=k:
                    require(left_data((a,b,j,k))==data,"semi exact low data")
                    require(sign((a,b,j,k))==p+a+b,"semi positive")
                    checks+=1
require(f(".102")+f(".100")+f(".015")==f(".217"),"full q2 level")
require(f(".317")<f(".3303"),"actual independent source length")
print(checks, "exact physical sign-reversal pairs and sieve levels passed")
