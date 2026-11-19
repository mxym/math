"""Finite deterministic checks for the 4-cycle pruning and EF implications.
This does not replace the probabilistic estimates. Standard library, no asserts."""
from itertools import combinations,permutations
from math import comb
def require(cond,msg):
 if not cond:raise ValueError(msg)
def do():
 n=3; vertices=list(range(2*n));R=range(n)
 free=[(i,j) for i in R for j in vertices if j!=i]
 all_=good=badedgecount=hallcases=ef=cycleproof=0
 for mask in range(1<<len(free)):
  rows=[1<<i for i in R]
  for bit,(i,j) in enumerate(free):
   if mask>>bit&1:rows[i]|=1<<j
  cyc=[]
  for i,h in combinations(R,2):
   shared=[j for j in vertices if (rows[i] & rows[h]) & (1<<j)]
   for x,y in combinations(shared,2):cyc.append({('r',i),('r',h),('c',x),('c',y)})
  dis=all(not(x&y) for x,y in combinations(cyc,2))
  arcs={(i,b) for i in R for b in range(n,2*n) if rows[i]>>b&1}
  bad={(i,b) for i,b in arcs if any(h!=i and rows[h]>>i&1 and rows[h]>>b&1 for h in R)}
  if dis:
   good+=1;require(len({i for i,b in bad})==len(bad)==len({b for i,b in bad}),'not a matching');badedgecount+=len(bad)
  for s in R:
   safe=all(not(rows[h]>>s&1) for h in R if h!=s)
   for pp in permutations([n,n+1]): # B side omits fixed dummy 2n-1
    rem=[i for i in R if i!=s];M=set(zip(rem,pp));hallcases+=1
    if safe and M <= arcs-bad:
     groups=[[i] for i in R]
     for i,b in M:groups[i].append(b)
     # Each true marked cost=1, otherwise 5. Row budget=2.
     cost=lambda h,G:sum(1 if rows[h]>>j&1 else 5 for j in G)
     require(all(cost(h,groups[h])<=cost(h,G) for h in R for G in groups),'envy')
     ef+=1
  all_+=1
 require(good and ef and badedgecount,'vacuous test')
 print(f'{all_} marked 3×6 arrays with a cheap diagonal in A; {good} with vertex-disjoint four-cycles; {badedgecount} bad arcs counted on these.')
 print(f'{hallcases} possible one-singleton/two-pair choices checked; all {ef} passing safe-singleton and pair pruning were independently EF.')
if __name__=='__main__':do()
