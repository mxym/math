"""Exact, standalone low-degree coefficients by upward flag extension on BCEL C(q,q^3)."""
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
import json
@lru_cache(None)
def sub(q,n,k):
    if k<0 or k>n:return 0
    if q==1:return comb(n,k)
    top=bottom=1
    for i in range(k):top*=q**(n-i)-1;bottom*=q**(k-i)-1
    return top//bottom
@lru_cache(None)
def chains(q,d,n,ranks):
    # Grow the flag from bottom to top, recording independent Boolean and linear rank increments.
    values={(0,0):1}
    for s in ranks:
        new={}
        for (a,b),old in values.items():
            for x in range(a,d+1):
                y=s-x
                if not b<=y<=n:continue
                new[x,y]=new.get((x,y),0)+old*sub(q,d-a,x-a)*comb(n-b,y-b)
        values=new
    return sum(values.values())
def small(q,k=4):
    r=3+k;n=q**3;c=q**6*comb(n,k)
    def f(*s):
        val=chains(q,6,n,s)
        if s and s[-1]==r-1:
            val+=c*(chains(q,3,k,s[:-1])-chains(q,3,k,s))
        return val
    z1=f(r-1)
    z2=f(r-2)+f(r-3,r-1)-f(r-3,r-2)
    z3=(f(r-3)+f(r-4,r-1)-f(r-4,r-3)+f(r-5,r-2)-f(r-5,r-3)
        +f(r-5,r-3,r-1)-f(r-5,r-3,r-2)-f(r-5,r-4,r-1)+f(r-5,r-4,r-3))
    return z1,z2,z3
def lead(v):
    # Exact finite-difference polynomial interpolation, inputs at 1,2,...; caller proves degree bound.
    d=0
    while v and not all(x==v[0] for x in v):v=[b-a for a,b in zip(v,v[1:])];d+=1
    if not v:raise ValueError('insufficient values')
    return d,str(Fraction(v[0],factorial(d)))
def main():
    rows={}
    for k,q in [(4,103),(3,149),(3,257)]:
        a,b,c=small(q,k)
        rows[f'rank{3+k}-q{q}']={'z1':a,'z2':b,'z3':c,'T2':b*b-a*c}
    for k in (3,4):
        v=[small(q,k) for q in range(1,36)]
        h=[lead([a[i] for a in v]) for i in range(3)]
        rows[f'rank{3+k}-leading-degrees-and-coefficients']=h
    print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
