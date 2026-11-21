#!/usr/bin/env python3
"""Independent signature-specific finite census through 10^8. Python standard library."""
from itertools import product
from math import lcm,isqrt
# Import previous exact matrix, known graph and arithmetic utilities. No caches required.
from check_eac_historical_jets import eac,invert,check
LIMIT=10**8
def primesieve(B):
 a=bytearray([1])*(B+1);a[:2]=b'\x00\x00'
 for p in range(2,isqrt(B)+1):
  if a[p]:a[p*p::p]=b'\x00'*((B-p*p)//p+1)
 return [p for p in range(2,B+1) if a[p]]
PRIMES=primesieve(isqrt(LIMIT))
def factor_bounded(n):
 r={}
 for p in PRIMES:
  if p*p>n:break
  if n%p==0:
   v=0
   while n%p==0:n//=p;v+=1
   r[p]=v
 if n>1:r[n]=1
 return r

def cap(r,w):
 cost=sum(-z for z in r if z<0); d=lcm(w.denominator,cost.denominator)
 target=LIMIT**int(d*w)*3**int(d*cost);mult=2**int(d*cost)
 a=1;b=LIMIT
 while a<b:
  c=(a+b)//2
  if c**d*mult>=target:b=c
  else:a=c+1
 return a

def candidates(N,root):
 C,A=eac(N);B=invert(A);k=len(C);rr=C.index(root)
 I=[rr]+[j for j,a in enumerate(A[rr]) if a]
 caps=[cap(B[j],sum(B[j])) for j in I]
 check(max(caps)<=PRIMES[-1],'table capacity for label bounds')
 choices=[[p for p in PRIMES if 3<=p<=size] for size in caps]
 total=consistent=complete=0;found=set()
 for row in product(*choices):
  if len(set(row))<len(row):continue
  n=row[0]+__import__('math').prod(q**A[rr][j] for j,q in zip(I[1:],row[1:]))
  if n>LIMIT:continue
  total+=1;lab=dict(zip(I,row)); good=True
  # Enforce the exact multiplicity of each known prime in every row with known input.
  for i,p in lab.items():
   diff=n-p
   if diff<=1:good=False;break
   for j,q in lab.items():
    rest=diff
    for _ in range(A[i][j]):
     if rest%q:good=False;break
     rest//=q
    if not good or rest%q==0:good=False;break
   if not good:break
  if not good:continue
  consistent+=1
  # Strong connectivity forces EVERY known label to occur in the reachability closure
  # of this one seed; this is only a necessary check, so cannot remove real realizations.
  todo=[row[0]];seen=set(todo)
  while todo and len(seen)<=k and good:
   p=todo.pop();fac=factor_bounded(n-p)
   if sum(fac.values())<2 or n%p==0:good=False;break
   for q in fac:
    if q not in seen: seen.add(q);todo.append(q)
  if good and len(seen)==k and set(row)<=seen:
   complete+=1; found.add(n)
 check(found=={N},'conservative frontier')
 # The literal historical realization is already verified by eac(N). Any remaining
 # initial assignment at the one center reaches its unique actual special component.
 print(N,'root',root,'caps',caps,'initial',total,'partial',consistent,'terminal',complete,'centers',sorted(found))

for N,root in [(128,3),(1718,3),(1862,3),(1928,3),(6142,17)]:candidates(N,root)
