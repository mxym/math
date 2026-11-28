"""Closed-form sign degrees vs independent sign-state DP and exact root witnesses."""
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from collections import Counter
def degree(w):
    zeros=[i for i,a in enumerate(w) if not a]
    non=[a*(-1)**sum(j>i for j in zeros) for i,a in enumerate(w) if a]
    return len(zeros)+sum(a!=b for a,b in zip(non,non[1:]))
def mindp(w):
    # Cross each node with mandatory odd/even zero orders or with fixed sign;
    # in each gap it costs one extra root to reverse sign. No location formula used.
    dp={-1:0,1:0}
    for i,s in enumerate(w):
        if not s:dp={z:min(dp.get(-z,1000)+1,dp.get(z,1000)+2) for z in [-1,1]}
        else:dp={s:dp.get(s,1000)}
        if i+1<len(w):dp={z:min(dp.get(z,1000),1+dp.get(-z,1000)) for z in [-1,1]}
    return min(dp.values())
def witness(xs,w):
    roots=[x for x,s in zip(xs,w) if not s]
    signs=[(x,s*(-1)**sum(r>x for r in roots)) for x,s in zip(xs,w) if s]
    new=[(a+b)/2 for (a,s),(b,t) in zip(signs,signs[1:]) if s!=t]
    rr=roots+new
    def sg(v):return (v>0)-(v<0)
    lead=1
    if signs:
        x=signs[0][0];i=xs.index(x)
        lead=w[i]*sg(prod(x-z for z in rr))
    assert [sg(lead*prod(x-z for z in rr)) for x in xs]==list(w)
    return len(rr)
def hullcount(groups):
    return max(len(T) for k in range(len(groups)+1) for T in combinations(groups,k)
               if all(max(a)<min(b) or max(b)<min(a) for a,b in combinations(T,2)))
def inspect(xs,groups):
    h=Counter();total=0
    for w in product([-1,0,1],repeat=len(xs)):
        d=degree(w);assert d==mindp(w)==witness(xs,w);total+=1
        if all(all(w[i]==0 for i in G) or min(w[i] for i in G)<0<max(w[i] for i in G) for G in groups):h[d]+=1
    return total,h,hullcount(groups)
specs=[("singleton",[-F(1,2),-F(1,6),F(0)],[[0],[1],[2]]),
       ("joint",[-F(1,2),-F(1,6),-F(1,12),F(0)],[[0,1],[2],[3]]),
       ("crossing",[-F(1,a) for a in (210,420,630,840,1050,1260)]+[F(0)],[[0,5],[1,2],[3,4],[6]])]
for name,xs,gs in specs:
    assert sorted(xs)==xs
    allw,h,mc=inspect(xs,gs)
    print(name,"all words",allw,"admissible",sum(h.values()),"minimum degree",min(h),"disjoint hulls",mc)
    if name=="crossing":
        assert h=={4:10,5:2,6:14,7:1} and mc==3
        print("crossing admissible degrees",sorted(h.items()))
