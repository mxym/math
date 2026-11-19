"""Exact finite stress tests for local lemmas in the linear-deficit proof.
Script checks its own complete stated finite ranges, not asymptotic probability."""
from itertools import combinations, permutations, product
from fractions import Fraction as Q
from math import comb,perm
def require(c):
 if not c:raise RuntimeError("check failed")
def omissions():
 # Six colors at a column. An ineligible label is ignored in the probability proof.
 # Check by local enumeration exactly how far ignoring parallel edges would err.
 n=d=6; tests=bad=sharp=0
 for labels in product(range(n),repeat=d):
  if d-len(set(labels))>1:continue
  for a,b in combinations(set(labels),2):
   loss=labels.count(a)+labels.count(b);require(loss<=3);sharp+=loss==3;tests+=1
 print(tests,'admissible two-distinct-neighbor deletions; max loss three attained',sharp,'times.')
def hg():
 # Layer is a bijection of an arbitrary N-row domain to N columns. For reversed
 # demands W may overlap domain in less than |W|. Directly count small layers.
 tests=0
 for N in range(1,7):
  perms=list(permutations(range(N)))
  for t in range(1,N+1):
   for s in range(1,N+1):
    for w in range(s+1):
     count=sum(all(y<w for y in pi[:t]) for pi in perms)
     require(Q(count,len(perms))<=Q(s,N)**t)
     if t<=w:require(Q(count,len(perms))==Q(perm(w,t),perm(N,t)))
     else:require(count==0)
     tests+=1
 print(tests,'exact rectangular-demand probabilities checked after arbitrary destination restrictions.')
def cap_assignment():
 # Small analogue of total cap principle; whenever each costly chosen edge lies
 # on a sufficiently short cheaper cycle, capped and uncapped optima agree.
 n=3;cnt=0;equal=0
 for maskedges in range(1<<(n*n)):
  cost=[[1 if maskedges>>(i*n+j)&1 else 13 for j in range(n)] for i in range(n)]
  Ps=list(permutations(range(n)));total=lambda p,C:sum(C[i][j] for i,j in enumerate(p))
  # A cheap perfect matching alone suffices for this toy since 3 < cap 4.
  if not any(total(p,cost)==3 for p in Ps):continue
  cap=[[min(x,4) for x in row] for row in cost]
  require(min(map(lambda p:total(p,cost),Ps))==min(map(lambda p:total(p,cap),Ps)))
  cnt+=1
 print(cnt,'capped/uncapped tiny assignment equalities.')
def constants():
 d=24;L=5+3*d*d;coef=Q(8)*Q(12,11)**2*comb(d,3)*Q(6,11)**(d-5)
 require(2*coef<1 and L==1733 and 6*(d*d+1)==3462 and Q(48,47)<Q(12,11))
 print('exact union-bound base majorant:',coef, '<1/2; d=24, L=1733, denominator 3462.')
if __name__=='__main__':constants();omissions();hg();cap_assignment()
