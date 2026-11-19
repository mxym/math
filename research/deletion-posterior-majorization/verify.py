"""Exact small-instance checks; no floating point or removable asserts."""
from collections import Counter
from itertools import product,combinations,accumulate
from math import comb

def must(p,msg):
 if not p: raise ArithmeticError(msg)

def run():
 words=prefixes=stricts=boundaries=0
 for q,N in [(2,10),(3,6),(4,5)]:
  for n in range(N+1):
   hosts=list(product(range(q),repeat=n))
   for m in range(n+1):
    masks=list(combinations(range(n),m)); B=comb(n,m); D=B*q**(n-m)
    # Generate each embedding from its actual mask, not from compression.
    hists={y:Counter() for y in product(range(q),repeat=m)}
    for x in hosts:
     counts=Counter(tuple(x[j] for j in I) for I in masks)
     for y,k in counts.items():hists[y][k]+=1
    def prefixes_for(h):
     return list(accumulate(k for k,f in sorted(h.items(),reverse=True) for _ in range(f)))
    hist0=Counter()
    for t in range(n+1):hist0[comb(t,m) if t>=m else 0]+=comb(n,t)*(q-1)**(n-t)
    base=prefixes_for(hist0);must(len(base)==q**n and base[-1]==D,"base length/sum")
    for y,h in hists.items():
     words+=1; h[0]=q**n-sum(h.values()); ps=prefixes_for(h)
     must(len(ps)==len(base) and ps[-1]==D,"posterior denominator")
     must(all(v<=w for v,w in zip(ps,base)),"prefix failure")
     prefixes+=len(ps)
     strict=(m<n and len(set(y))>1)
     must((ps!=base)==strict and (ps[0]<base[0])==strict,"strict/equality")
     must(h[0]==hist0[0],"order zero")
     stricts+=strict;boundaries+=(n==m or m==0)
 return words,prefixes,stricts,boundaries

if __name__=="__main__":
 a,b,c,d=run()
 print(f"PASS: {a} ordered (q,n,m,observed word) checks, {b} exact majorization prefix sums, {c} strict/nonconstant, {d} empty/no-deletion boundaries.")
