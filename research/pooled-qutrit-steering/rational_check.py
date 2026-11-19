from fractions import Fraction as F
from itertools import combinations

def require(x):
    if not x:
        raise RuntimeError("exact check failed")
# Average minimum from the elementary tail integral (1-3t)^2.
T=F(1,3)
mean=T-3*T*T+3*T*T*T
s=F(2,27)
pair_prob=6*s*s
threshold=1-3*(mean+pair_prob*s/2)/(1+pair_prob/2)
require(mean==F(1,9) and threshold==F(1486,2223))
# Independent finite check: cap dual at all pooled breakpoints, including ties.
cases=[(0,0,1),(1,1,1),(1,2,8),(3,1,7),(6,3,5)]
tests=0
for size in (1,2,3):
    for bases in combinations(cases,size):
        triples=[tuple(F(x,sum(b)) for x in b) for b in bases]
        pooled=sorted(p for b in triples for p in b)
        G=sum(pooled[:size])/size
        alpha=sum(min(b) for b in triples)/size
        beta=F(sum(sorted(b)[1]<=s for b in triples),size)
        dual=lambda t:t-sum((max(F(0),t-p) for p in pooled), F(0))/size
        require(G==max(map(dual,[F(0),*pooled,F(1)])))
        require(alpha-G>=beta*(alpha-s)/(1+beta))
        tests+=1
print(f"mean minimum={mean}; pooled additive visibility gap={threshold-F(2,3)}; threshold={threshold}; {tests} exact finite dual replays; PASS")
