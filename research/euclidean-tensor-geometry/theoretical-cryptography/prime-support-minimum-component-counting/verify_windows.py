"""Exact finite component counts by sieve and independent twin-pair Euler products."""
from itertools import combinations
from math import isqrt,prod
X=16384
primes=[p for p in range(2,X+1) if all(p%a for a in range(2,isqrt(p)+1))]
support=[[] for _ in range(X+1)]
for p in primes:
    for v in range(p,X+1,p): support[v].append(p)
def ok(S,H,s):
    if not S: return False
    groups=[1]
    for p,q in zip(S,S[1:]):
        if q-p<=H: groups[-1]+=1
        else: groups.append(1)
    return min(groups)>=s
A={(H,s):sum(ok(P,H,s) for P in support[2:]) for H in (1,2) for s in (2,3,4)}
# Width=2: past 7 every non-singleton component is a disjoint twin pair.
# Multiply the Euler factors, truncated at X. Enumerate {2,3,5,7} separately.
def powers(S,cap):
    if not S: return {1}
    p,*rest=S;ans=set();right=powers(rest,cap)
    q=p
    while q<=cap:
        ans|={q*v for v in right if q*v<=cap};q*=p
    return ans
Pset=set(primes)
for s in (2,3,4):
    V={1}
    for j in range(1,5):
        for S in combinations((2,3,5,7),j):
            if ok(S,2,s): V.update(powers(S,X))
    if s==2:
        for p in primes:
            if p<=7 or p+2 not in Pset: continue
            if p*(p+2)>X: break
            add=powers([p,p+2],X)
            V|={n*v for n in V for v in add if n*v<=X}
    assert len(V)-1==A[2,s]
assert A[1,2]==len(powers([2,3],X)) and A[1,3]==A[1,4]==0
print("PASS: X",X,"fixed widths 1 and 2 by s=2,3,4",
      [A[H,s] for H in (1,2) for s in (2,3,4)])
