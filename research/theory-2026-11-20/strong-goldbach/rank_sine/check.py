"""Exact finite checks on the normalization identities and lower bounds; not a proof by sampling."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import factorial as fac

def must(value, what):
    if not value:
        raise ValueError(what)

def atan_bounds(z,n):
    t=sum(((-1)**j*z**(2*j+1)/(2*j+1) for j in range(n)),F())
    other=t+(-1)**n*z**(2*n+1)/(2*n+1)
    return min(t,other),max(t,other)

a,b=atan_bounds(F(1,5),12)
c,d=atan_bounds(F(1,239),4)
pi_low,pi_up=16*a-4*d,16*b-4*c
must(F(314159,100000)<pi_low<pi_up<F(314160,100000),"Machin bounds")
must(pi_low**6/360>F(267,100),"3x5 debit")
b_R=sum((pi_low**(k-1)/fac(k) for k in (3,7,11,15)),F())
must(2*b_R*b_R>F(675,100),"all-sign bound from ranks ≤15")

def divs(w):
    counts=[1]
    for t in w:
        nxt=counts+[0]*t
        for i,c in enumerate(counts): nxt[i+t]-=c
        counts=nxt
    return counts

rows=0
for k in range(1,8):
    for w in combinations_with_replacement(range(1,8),k):
        rows+=1
        total=sum(w)
        c=divs(w)
        # Exact v-integral over (0,1), ignoring the finitely many endpoints.
        s=0; vtot=0
        for j in range(total):
            s+=c[j]
            vtot+=s
        must(vtot==total*(k==1),"uniform threshold")
        # Half-cut complement symmetry if equality has zero coefficient.
        if k%2==0 and (total%2 or c[total//2]==0):
            must(sum(c[:(total+1)//2])==0,"even half")
        if k==3 and total!=2*max(w):
            must(sum(c[:(total+1)//2])==(-2 if total>2*max(w) else 0),"triprime half")

print(f"PASS: {rows} integer profiles, exact integrated thresholds, half cuts, π^6/360>2.67, exact ranks through 15 force >6.75.")
