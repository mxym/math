"""Exact corroboration, not a computer proof: standard library, fail closed."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import comb, factorial,prod

def equal(x,y):
    if x!=y: raise ArithmeticError((x,y))
def need(x):
    if not x: raise ArithmeticError("strict sign or bound failed")

# Canonical reduced shapes. () is one leaf, None is empty.
def join(x,y):
    if x is None: return y
    if y is None: return x
    return tuple(sorted((x,y)))
@lru_cache(None)
def cat(n):
    return join((),cat(n-1)) if n>1 else (() if n==1 else None)
even=join(cat(3),cat(3))
@lru_cache(None)
def shapes(n):
    if n==1:return ((),)
    return tuple(sorted({join(t,h) for a in range(1,n//2+1) for t in shapes(a) for h in shapes(n-a)}))
def label(t,idx):
    if t==():return next(idx)
    return (label(t[0],idx),label(t[1],idx))
def sample(t,occupancy):
    if isinstance(t,int):return cat(occupancy[t])
    return join(sample(t[0],occupancy),sample(t[1],occupancy))
@lru_cache(None)
def exact_finite(t): # DP counts all leaf subsets by shapes
    if t==():return Counter({None:1,():1})
    L,R=map(exact_finite,t);d=Counter()
    for a,ma in L.items():
        for b,mb in R.items():d[join(a,b)]+=ma*mb
    return d
def check_finite():
    seen=tests=subsets=0
    for n in range(1,11):
        for t in shapes(n):
            seen+=1;tl=label(t,iter(range(n)));dp=exact_finite(t)
            for j in range(min(7,n)+1):
                tests+=1; hist=Counter()
                for chosen in combinations(range(n),j):
                    x=[0]*n
                    for i in chosen:x[i]=1
                    hist[sample(tl,x)]+=1
                subsets+=sum(hist.values())
                equal(sum(hist.values()),comb(n,j))
                for s in ((None,) if j==0 else shapes(j)):equal(dp[s],hist[s])
    print("Finite root-split counts = direct induced leaf subsets:",seen,"shapes;",tests,"(tree,size) pairs;",subsets,"subsets.")

def comps(n,k):
    if k==1:yield (n,);return
    for i in range(n+1):
        for tail in comps(n-i,k-1):yield (i,)+tail
def mult(j,tl,weights):
    hist=Counter()
    for c in comps(j,len(weights)):
        coeff=factorial(j)//prod(factorial(i) for i in c)
        hist[sample(tl,c)]+=coeff*prod(w**i for w,i in zip(weights,c))
    equal(sum(hist.values()),1)
    return hist
def F(j,p):
    q=1-p
    return p**j+q**j+j*(p*q**(j-1)+q*p**(j-1))
def H(p):
    return 20*(p*(1-p))**3
def Ft(j,p):
    return F(j,p)-p**j*(1-F(j,Q(1,2)))-j*(1-p)*p**(j-1)*(1-F(j-1,Q(1,2)))
def Ht(p):
    return H(p)+Q(5,16)*p**6
def check_mult():
    total=0
    for leaves in range(2,6):
        for t in shapes(leaves):
            tl=label(t,iter(range(leaves)))
            for c in comps(8-leaves,leaves):
                weights=[Q(i+1,8) for i in c]
                ds=[1-mult(j,tl,weights)[cat(j)] for j in (4,5,6)]
                S=mult(6,tl,weights)[even]/20
                for lhs,rhs in [(ds[0]**3,216*S**2),(ds[1]**3,1000*S**2),((ds[2]+10*S)**3,3375*S**2)]:
                    need(lhs>=rhs)
                    if leaves==2:equal(lhs,rhs)
                if leaves==2:
                    for j in (4,5,6,7):equal(mult(j,tl,weights)[cat(j)],F(j,weights[0]))
                    equal(20*S,H(weights[0]))
                total+=1
    print("Three sharp inequalities via multinomial enumeration:",total,"weighted skeletons; all two-terminal equalities hold.")
    k=7;p=Q(1,1024);s=p-p**(k-2)
    for a in [p,s]:
        w=(a/2,a/2,1-a);tl=((0,1),2)
        equal(mult(k,tl,w)[cat(k)],Ft(k,a))
        equal(mult(6,tl,w)[even],Ht(a))
    gaps=[Ft(k,s)-F(k,p),F(k,p)-Ft(k,p),Ht(s)-H(p)]
    for g in gaps:need(g>0)
    print("k=7 exact matched-coordinate witness: p=1/1024, s=p-p^5.")
    print("Three positive gaps Ft(s)-F(p), F(p)-Ft(p), Ht(s)-H(p):")
    for g in gaps:print(g)
    print("Ft continuous; Ht increasing on [s,p]. Thus a matching a strictly improves H.")
if __name__=="__main__":check_finite();check_mult()
