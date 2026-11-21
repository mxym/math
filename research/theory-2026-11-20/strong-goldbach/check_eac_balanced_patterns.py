#!/usr/bin/env python3
"""Exact table-based classification of all possible linear families, for the cutoff 53."""
from check_eac_sunits import P,walk,chk
from pathlib import Path
from itertools import combinations
from math import gcd
from collections import Counter
import sys
def peel(n):
 f=set()
 for p in P:
  while n%p==0:f.add(p);n//=p
 return n,f
def table_candidates(folder):
 # Direct orientation: N'=p+g*c. Since N'=p+q+h*p*q, one has 
 # h=(g*c-q)/(p*q). Do not preselect/reuse an old list of h values.
 pairs={}
 for p,q in combinations(P,2):
  for g in range(1,q-p+1,2):
   if (q-p)%g==0:pairs.setdefault((q-p)//g,[]).append((p,q,g))
 rows=0;H=set()
 for a,b,c in walk(folder,0):
  if c%2==0:continue
  edge=a if a%2==0 else b
  for p,q,g in pairs.get(edge,()):
   h,r=divmod(g*c-q,p*q)
   if h>=2 and r==0 and h%2==0:
    chk(peel(h*p+1)[0]==1 and peel(h*q+1)[0]==1,'table reconstruction')
    H.add(h);rows+=1
 return rows,H
def check():
 data=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).parent
 n,H=table_candidates(data);print('source triples with pair and multiplier',n,'distinct positive even h',len(H),'maximum',max(H))
 chk(len(H)==1488 and max(H)==1861842140,'multiplier counts')
 patterns=set()
 for h in sorted(H):
  fac={}
  for p in P:
   r,f=peel(h*p+1)
   if r==1:fac[p]=f
  # Exhaust all subsets of eligible small labels, without assuming strong
  # connectedness or forbidding primes dividing h at this stage.
  for k in range(2,len(fac)+1):
   for C in combinations(sorted(fac),k):
    S=set(C)
    if all(fac[p]<=S for p in C):patterns.add((h,C))
 base={3,5,7,11,13,19,23,47};opt={17,31,37}
 expect={(56,(3,13))}|{(2,tuple(sorted(base|set(V)))) for k in range(4) for V in combinations(opt,k)}
 chk(patterns==expect,sorted(patterns-expect))
 print('multiplier and alphabet patterns:',sorted(patterns))
 # Finite square-class obstruction for h=56.
 chk({pow(3,j,16) for j in range(4)}=={1,3,9,11},'order four')
 chk(all((i%2,j%2)==(0,0) for i in range(4) for j in range(4) if pow(3,i,16)*pow(13,j,16)%16==1),'parities')
if __name__=='__main__':check()
