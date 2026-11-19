"""Exact finite tests, not a numerical proof of regular-variation asymptotics."""
from itertools import product
from functools import lru_cache
from math import comb
from fractions import Fraction as Q

def require(x):
    if not x: raise ArithmeticError("rational check failed")
P=[Q(j,4) for j in range(5)]
schedule_count=cap_count=block_count=0
for r in [1,2]:
    mu=Q(1,1+r)
    def cost(p):return p**r/(1+r)
    def act(p,v):return p*cost(p)+(1-p)*v
    def pay(seq):
        v=mu
        for p in reversed(seq):v=act(p,v)
        return v
    def block(m,v):return min(cost(p)*(1-(1-p)**m)+(1-p)**m*v for p in P)
    for N in range(1,7):
        scores={};sorted_scores={}
        for seq in product(P,repeat=N):
            v=pay(seq); vs=pay(sorted(seq))
            require(vs<=v)
            k=len(set(seq))
            scores[k]=min(scores.get(k,v),v)
            sorted_scores[k]=min(sorted_scores.get(k,vs),vs)
            schedule_count+=1
        for k in range(1,min(N,len(P))+1):
            truth=min(v for j,v in scores.items() if j<=k)
            require(truth==min(v for j,v in sorted_scores.items() if j<=k))
            @lru_cache(None)
            def memo(remaining,mask):
                if not remaining:return mu
                return min(act(p,memo(remaining-1,mask|(1<<i))) for i,p in enumerate(P)
                           if (mask&(1<<i)) or mask.bit_count()<k)
            require(memo(N,0)==truth)
            lo=hi=mu
            for j in range(k):
                lo=block(N+1,lo);hi=block(N//k,hi)
            require(lo<=truth<=hi);cap_count+=1
        for p in P:
            # Independently use first success index, not recursively merging stages.
            v=Q(1,7)
            direct=sum((1-p)**j*p*cost(p) for j in range(N))+(1-p)**N*v
            require(direct==cost(p)*(1-(1-p)**N)+(1-p)**N*v)
            block_count+=1
    for n in range(1,15):
        # Integral after binomial expansion against quantile u^r vs beta product.
        v=sum(n*Q((-1)**j*comb(n-1,j),r+j+1) for j in range(n))
        require(v==1/Q(comb(n+r,r)))
print(f"Exactly sorted/compared {schedule_count} quantile schedules, {cap_count} menu/horizon/budget comparisons, {block_count} one-block formulas.")
print("Verified 28 power-quantile order-statistic beta integrals.")
