"""Exact finite corroboration, Python 3 standard library only. Not an asymptotic proof."""
from fractions import Fraction as F
from itertools import combinations
from math import comb, isqrt, prod
from functools import lru_cache
from bisect import bisect_left
from collections import Counter

def require(b):
    if not b: raise ArithmeticError('failed exact check')

@lru_cache(maxsize=1024)
def binom(N,p):
    a,b=p.numerator,p.denominator
    return tuple(comb(N,i)*a**i*(b-a)**(N-i) for i in range(N+1))

def Jof(u,v):return (u-1,u,v,v+1)
def Jall(N):
    return [(u,v,Jof(u,v)) for u in range(1,N) for v in range(u+1,N)]

@lru_cache(maxsize=16384)
def signs_coeff(N,J):
    return tuple(tuple((1 if (len(J)-1-i)%2==0 else -1)*prod(x-j for j in J if j!=s)
                       for x in range(N+1)) for i,s in enumerate(J))
def signs(N,J,p):
    masses=binom(N,p)
    return tuple(sum(a*b for a,b in zip(row,masses)) for row in signs_coeff(N,J))
def sig(x):return (x>0)-(x<0)
def classification(N,u,v):
    C=N*(N-1)-(u+v-N)**2; d=v-u
    return sig(C-d*d*(N-1)),sig((d+2)**2*(N-1)-C)
def centers(N,s):
    if not 3<=s<=2*N-3:return None
    h=N*(N-1)-(s-N)**2
    d=isqrt((h-1)//(N-1)) # strict lower root
    if (d-s)%2:d-=1
    if d<1 or (d+2)**2*(N-1)<=h:return None
    u,v=(s-d)//2,(s+d)//2
    if not (1<=u<v<=N-1):return None
    return Jof(u,v)
def nearest(n,p):
    N=n-1
    z=max(F(3),min(F(2*N-3),1+2*(N-1)*p))
    lo=z.numerator//z.denominator; hi=-((-z.numerator)//z.denominator)
    return (centers(N,lo) or centers(N,lo-1),centers(N,hi) or centers(N,hi+1))
def qvalue(n,J,masses):
    return F(sum(m*prod(x-j for j in J) for x,m in enumerate(masses)),prod(n-j for j in J))
counts=Counter()
for N in range(4,45):
    records=Jall(N); active=[]
    for u,v,J in records:
        p=F(u+v-1,2*(N-1)); a,b=classification(N,u,v)
        z=signs(N,J,p)
        require(tuple(map(sig,z))==(a,b,b,a))
        if a>0 and b>0:
            active.append((u+v,J))
            require(centers(N,u+v)==J)
        if a*b==0:
            require(a>=0 and b>=0)
            require(any(x<0 for x in signs(N,J,p-p/97)))
            require(any(x<0 for x in signs(N,J,p+(1-p)/97)))
            counts['isolated']+=1
        counts['centers']+=1
    active.sort()
    require(active[0][0]==3 and active[-1][0]==2*N-3)
    for (s,j),(t,k) in zip(active,active[1:]):
        require(t-s in (1,2))
        require(all(y-x in (0,1) for x,y in zip(j,k)) and j<k)
    if N>=5:require(max(j[-1]-j[0] for s,j in active)==isqrt(N-1)+2)
    if N<=17:
        for a in range(52):
            p=F(a,51);masses=binom(N+1,p)
            l,r=nearest(N+1,p);require(l is not None and r is not None)
            want=min(qvalue(N+1,J,masses) for u,v,J in records)
            require(want==min(qvalue(N+1,J,masses) for J in {l,r}))
            counts['two_center_vs_all']+=1
# Test phase order and unique positive support directly on exact rational probes, for every small even k
for N in range(2,12):
    for k in range(2,N+1,2):
        bases=[tuple(i for a in st for i in (a,a+1))
               for st in combinations(range(N),k//2) if all(b>=a+2 for a,b in zip(st,st[1:]))]
        prev=None
        for num in range(1,97):
            p=F(num,97); hit=[]
            for J in bases:
                z=signs(N,J,p)
                if min(z)>=0: hit.append((J,tuple(i for i,x in zip(J,z) if x>0)))
            require(hit and len({x[1] for x in hit})==1)
            if len(hit)==1 and hit[0][0]==hit[0][1]:
                current=hit[0][0]
                if prev is not None:
                    require(all(x<=y for x,y in zip(prev,current)))
                prev=current
            counts['all_basis_parameter_probes']+=1
print('PASS: direct integer binomial/Lagrange sums and complete small dual comparisons')
for k in sorted(counts):print(k,counts[k])
