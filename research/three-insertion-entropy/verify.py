#!/usr/bin/env python3
"""Integer-only finite elimination for the three-insertion entropy comparison.
Python 3 standard library; check raises under -O. A reception has n symbols.
"""
from collections import Counter
from itertools import combinations
from math import comb, prod

def check(c, msg):
    if not c: raise ArithmeticError(msg)

def expf(a):
    return a**a if a>=1 else 1

def segment(n,l):
    return expf(max(0,l-1))**(n-l)*expf(max(0,l-2))**max(0,l-2)

def mask_polynomial(lengths):
    y=[]
    for t in lengths:
        b = y[-1] if y else 0
        y += [b^(j%2) for j in range(t)]
    n=len(y);x=sum(v<<(n-j-1) for j,v in enumerate(y))
    def erase(x,i):return ((x>>(i+1))<<i)|(x% (1<<i))
    counts=Counter(erase(erase(erase(x,k),j),i) for i,j,k in combinations(range(n),3))
    check(sum(counts.values())==comb(n,3),'mask sum')
    return prod(expf(v)**u for v,u in Counter(counts.values()).items())

def finite():
    totals=Counter(); direct=Counter(); coarse=Counter()
    for n in range(7,130):
        m=n-2; target=m**(m*m)
        for ell in (1,2):
            if m<16:  # one equal bond touching or next to a boundary
                check(mask_polynomial((ell,n-ell))>target,(n,ell))
                totals['one-bond boundary direct']+=1
        for D in range(2,n):
            b=D+1; runcost=1<<(D*m*(m-1))
            # Bound first; only construct the integer if the exponent is modest.
            if runcost>target:
                totals['(n,D) run only']+=1
                continue
            q,r=divmod(n,b)
            g=[segment(n,i) for i in range(n+1)] # i>=1 is used
            # Consecutive log-convexity of the integer factors; this finite check
            # proves the balancing step independently of any calculus.
            check(all(g[l]**2<=g[l-1]*g[l+1] for l in range(2,n)),(n,'convex'))
            if runcost*g[q]**(b-r)*g[q+1]**r>target:
                totals['(n,D) balanced lower']+=1;continue
            coarse[n,D]+=1
            for cut in combinations(range(1,n),D):
                L=tuple(y-x for x,y in zip((0,)+cut,cut+(n,)))
                if runcost*prod(g[l] for l in L)>target:
                    totals['ordered compositions run+block']+=1;continue
                check(mask_polynomial(L)>target,('failed strict',n,L))
                direct[n,D]+=1
    print('n=7..129, # finite cases by proof:',dict(totals))
    print('residual direct word counts (complements automatic):',sum(direct.values()))
    print(list(direct.items()))

if __name__=='__main__':finite()
