"""Verify deterministic singleton certificates on exact instances and finite-depth numerical witnesses.
Only the analytic proof establishes the asymptotic and quantifier statements."""
from fractions import Fraction as F
from itertools import permutations,product
from random import Random
def check(b,m):
 if not b:raise ValueError(m)
def requests(rows):
 lists=[sorted(range(len(r)),key=r.__getitem__) for r in rows]
 lists=[[x for x in l if r[x]<r[l[0]]+r[l[1]]] for l,r in zip(lists,rows)]
 n=len(rows); m=len(rows[0]); R=[set() for _ in range(m)]
 for _ in range(m*n+2):
  T=[set() for _ in range(m)]
  for i,l in enumerate(lists):
   for h in l:
    T[h].add(i)
    if not R[h]-{i}:break
  if R==T:return R
  check(all(a<=b for a,b in zip(R,T)),'not monotone');R=T
 raise ArithmeticError('did not stabilize')
def audit(rows):
 n=len(rows);m=len(rows[0]);R=requests(rows);count=owned=0
 for alloc in product(range(n),repeat=m):
  bundles=[[j for j,v in enumerate(alloc) if v==i] for i in range(n)]
  if not all(bundles):continue
  if any(any(sum(r[j] for j in B)<sum(r[j] for j in bundles[i]) for B in bundles) for i,r in enumerate(rows)):continue
  count+=1
  for i,b in enumerate(bundles):
   if len(b)==1:check(not R[b[0]]-{i},'false owner');owned+=1
 return count,owned
rng=Random(10041); prof=tot=own=0
for m,n,shapes,nsamp in [
 (3,2,[(1,2,5),(2,3,4)],100),(4,3,[(1,2,5,8),(3,5,7,11),(6,8,9,12)],520),
 (5,3,[(1,2,5,8,11),(3,5,7,11,13),(6,8,9,12,13)],190)]:
 for t in range(nsamp):
  rows=[rng.sample(shapes[rng.randrange(len(shapes))],m) for _ in range(n)]
  a,b=audit(rows);tot+=a;own+=b;prof+=1
check(own>100 and tot>100,'vacuous regression')
print('PASS:',prof,'integer markets with all allocations enumerated;',tot,'EF allocations,',own,'singleton-owner checks.')
# Rational lower estimates for exp(z), rounded downward between iterations; avoid floating comparisons.
def witness(c,K,T):
 p=F();M=10**13
 for _ in range(T):
  z=F(9,10)/c*sum(p**j for j in range(K));z=F((z*M)//1,M)
  e=term=F(1)
  for i in range(1,121):term*=z/i;e+=term
  p=F(((1-1/e)*M)//1,M);f=1-(1+z)/e
 check(f>2*(1-1/c),'strict infeasibility witness')
 return F((f*10**6)//1,10**6)
for c,K,t in [(F(11,10),8,1),(F(3,2),8,4),(F(19,10),16,8),(F(199,100),32,9),(F(1999,1000),32,9)]:
 f=witness(c,K,t);print('PASS: c=',c,'K=',K,'t=',t,'forced fraction >=',f)
