#!/usr/bin/env python3
"""Exact rank-nine minimum certificate. Use --with-envelope to replay the prior slope filter."""
from functools import lru_cache
from itertools import combinations
from math import comb
import sys


def require(test, msg):
    if not test:
        raise AssertionError(msg)


def C(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def partitions(n, low=1):
    if n == 0:
        yield ()
    else:
        for a in range(low, n+1):
            for p in partitions(n-a, a):
                yield (a,) + p


def multipartite_F(p):
    f=[1,0,0,0,0]
    for a in p:
        for j in range(4,0,-1):
            f[j] += a*f[j-1]
    return f[2]+f[3]-f[4]


def shadow_and_completion(t):
    """Minimum 2-shadow and maximum all-triples 4-completion via 3-binomial form."""
    lower=upper=0
    prev=100
    for j in (3,2,1):
        if t == 0:
            break
        v=j
        while comb(v+1,j) <= t:
            v += 1
        require(v < prev, "strict decrease in binomial expansion")
        prev=v
        t -= comb(v,j)
        lower += C(v,j-1)
        upper += C(v,j+1)
    require(t == 0, "binomial expansion complete")
    return lower,upper


def tuples_in_budget(weights, budget):
    if not weights:
        yield ()
    else:
        for i in range(budget//weights[0]+1):
            for rest in tuples_in_budget(weights[1:],budget-i*weights[0]):
                yield (i,) + rest


VLOSS=tuple(2-C(d,2)+C(d,3) for d in range(10))
VGAIN=tuple(C(d,4)-C(d,3) for d in range(10))
ELOSS=tuple(1-d+C(d,2) for d in range(10))
EGAIN=tuple(C(d,3)-C(d,2) for d in range(10))
TGAIN=tuple(C(d,2)-d for d in range(10))
VERTS=tuple(next(v for v in range(10) if C(v,2)>=e) for e in range(37))


@lru_cache(None)
def best_vertices(requirements, budget):
    if not requirements:
        return 0
    states=[]
    for d in range(requirements[0],8):
        if VLOSS[d] <= budget:
            tail=best_vertices(requirements[1:],budget-VLOSS[d])
            if tail is not None:
                states.append(VGAIN[d]+tail)
    return max(states,default=None)


def aggregate():
    pp=list(partitions(9))
    require(len(pp)==30 and max(map(multipartite_F,pp))==54, "outside F bound")
    require(all(x>=0 for x in VLOSS+ELOSS),"clique deficits are nonnegative")
    require(max(VGAIN[:8])==0, "uncharged singletons cannot raise the objective")
    require(min(VLOSS[8:])>=30, "singleton cap")
    require(min(ELOSS[7:])+2*min(VLOSS[7:])>29, "edge cap")
    require(6+3*min(ELOSS[6:])>29, "triangle cap")

    Sh=[shadow_and_completion(t) for t in range(30)]
    table=[None]*30
    tested=valid=0
    for ts in tuples_in_budget((1,2,3,4,5),29):
        L3=sum(d*t for d,t in enumerate(ts,1))
        B3=sum(t*TGAIN[d] for d,t in enumerate(ts,1))
        for es in tuples_in_budget(ELOSS[3:7],29-L3):
            tested+=1
            L2=sum(e*ELOSS[d] for d,e in enumerate(es,3))
            tail_edges=tuple(sum(es[i:]) for i in range(4))
            if any(tail_edges[d-3] < Sh[sum(ts[d-1:])][0] for d in (3,4,5)):
                continue
            # d=2 edges cost no deficit and contribute -1, so use their
            # smallest possible number given the 2-shadow.
            e2=max(0,Sh[sum(ts[1:])][0]-tail_edges[0])
            B2=sum(e*EGAIN[d] for d,e in enumerate(es,3))+e2*EGAIN[2]
            r=tuple(VERTS[e] for e in tail_edges)+(0,)
            req=tuple(d for d in (3,4,5,6) for _ in range(r[d-3]-r[d-2]))
            V=best_vertices(req,29-L3-L2)
            if V is None:
                continue
            valid+=1
            b=B2+B3+V+Sh[L3][1]
            if table[L3] is None or b>table[L3]:
                table[L3]=b
            require(b<=0,(ts,es,e2,req,b))
    require(max(x for x in table if x is not None)==0, "zero maximum")
    print("PASS rank-nine local certificate",tested,valid,table)


def witness():
    H=[0]*19
    def add(i,j):
        H[i] |= 1<<j
        H[j] |= 1<<i
    for i,j in combinations(range(10),2):
        if {i,j}!={0,1}: add(i,j)
    for i in range(10,19):
        g=(i-10)//3
        for j in ((2,3,5),(3,4,6),(2,4,7))[g]: add(i,j)
        for j in range(10,i):
            if (j-10)//3!=g: add(i,j)
    n=(1<<19)-1
    ok=[True]+[False]*n
    counts=[0]*20
    for S in range(n+1):
        if S:
            b=S&-S; R=S^b
            ok[S]=ok[R] and R & H[b.bit_length()-1]==R
        if ok[S]: counts[S.bit_count()]+=1
    require(counts==[1,19,98,193,191,196,140,64,17,2]+[0]*10,"19-point clique vector")
    reached={0}
    while True:
        more=reached|{j for i in reached for j in range(19) if i!=j and H[i]>>j&1==0}
        if more==reached: break
        reached=more
    require(len(reached)==19,"connected complement")
    print("PASS 19-point connected witness")


def envelope():
    from verify_independence_polynomial_finite_followups import possible
    result=possible(18,9)
    require((len(result),min(result),max(result))==(58,62,119),"prior edge range")
    crossing=set().union(*result.values())
    require({k for k,v in crossing}=={4} and min(v for k,v in crossing)==175,
            "prior first post-drop rise")
    print("PASS prior 18-point rank-nine slope envelope")


if __name__=="__main__":
    aggregate()
    witness()
    if "--with-envelope" in sys.argv:
        envelope()
