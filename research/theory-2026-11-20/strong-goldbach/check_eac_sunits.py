#!/usr/bin/env python3
"""Check the two exact full-height compact-core conclusions against pinned public rational S-unit tables; no searches up to N."""
import argparse, hashlib, math, os
from pathlib import Path
from itertools import combinations
P=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53)
DATS=(
 ('abc53.original.txt','80f3cd4e2535285f9a5c5811d9646b60523f7caef6fb0506202af761a743da98',1663449),
 ('abc1e7.original.txt','c28a87a2015c987d6665647117094cab4e9072a7d23301c5d89f892d3d2b2fb3',432408))
def chk(ok,detail):
 if not ok:raise ValueError(detail)
def walk(path,which):
 name,expected,count=DATS[which];h=hashlib.sha256();n=0
 with (path/name).open('rb') as f:
  for line in f:
   h.update(line)
   if line.startswith(b'#'):continue
   rad,A,plus,B,eq,C,quality=line.split()
   a,b,c=map(int,(A,B,C));chk(plus==b'+' and eq==b'=' and a+b==c and 0<a<=b and math.gcd(a,b)==1,'bad abc');n+=1
   yield a,b,c
 chk(n==count and h.hexdigest()==expected,('file integrity',name,n,h.hexdigest()))
def stablerecurrent(n):
 E={}
 for p in P:
  if not 3<=p<=n-3 or n%p==0:continue
  m=n-p;pf=set();k=0
  for q in P:
   while m%q==0:m//=q;k+=1;pf.add(q)
  if m==1 and k>=2:E[p]=pf
 # E maps a complete/composite row to all its true prime factors.
 S=set(E)
 while True:
  U={p for p in S if E[p]<=S}
  if U==S:break
  S=U
 def reach(p):
  R={p};W=[p]
  for q in W:
   for r in E[q]-R:R.add(r);W.append(r)
  return R
 C={p:reach(p) for p in S};out=set()
 for p,R in C.items():
  if all(C[q]==R for q in R):
   chk(len(R)>1,(n,p,'nonunit singleton?'))
   out.add(tuple(sorted(R)))
 return sorted(out)
def compact(path):
 pairs=list(combinations(P,2))
 # Table orientations: the even one of the summands is the normalized row gap.
 allow={}
 for p,q in pairs:
  delta=q-p
  for g in range(1,delta+1,2):
   if delta%g==0:allow.setdefault(delta//g,[]).append((p,q,g))
 centers=set();best=(0,None);eligible=0
 for a,b,c in walk(path,0):
  if c%2==0:continue
  t=b if a%2 else a
  if t in allow:
   eligible+=1
   for p,q,g in allow[t]:
    n=p+g*c;chk(n>q and n%2==0 and (n-q)==g*(c-t),'reconstruction')
    centers.add(n)
    if n>best[0]:best=(n,(p,q,g,a,b,c))
 chk((eligible,len(centers),best)==(5630,36476,(4020958408470,(3,47,11,4,365541673493,365541673497))),(eligible,len(centers),best))
 cores=[(n,C) for n in sorted(centers) for C in stablerecurrent(n)]
 chk(cores==[(128,(3,5,7,11,13,23,29,41)),(2200,(3,13))],cores)
 print('53-smooth normalized even small-gap triples:',eligible,'even centers:',len(centers),'maximum:',best)
 print('All exceptional compact closed SCCs:',cores)
def radical(path):
 maximum=(0,1);label=None
 for a,b,c in walk(path,1):
  if c%2==0:continue
  t=b if a%2 else a
  if c*maximum[1]>maximum[0]*t:maximum=c,t;label=a,b,c
 chk((maximum,label)==((162089505,4),(4,162089501,162089505)),(maximum,label))
 print('radical <= 10^7 max odd larger complement / even normalized gap:',maximum,label)
 # Exhaust the elementary cut R<91869 for sets of three or more distinct odd primes.
 limit=91869;sp=list(range(limit+1));rad=[1]*(limit+1)
 for p in range(2,limit+1):
  if sp[p]==p:
   for j in range(p,limit+1,p):rad[j]*=p
   for j in range(p*p,limit+1,p):
    if sp[j]==j:sp[j]=p
 for r in range(105,limit+1,2):
  if r!=rad[r]:continue
  z=r;f=[]
  while z>1:p=sp[z];f.append(p);z//=p
  if len(f)<3:continue
  s=min(r*(rad[q-p]//math.gcd(r,rad[q-p])) for p,q in combinations(f,2))
  chk(s<=10**7 or (r==limit and f==[3,113,271] and s==10105590),(r,f,s))
 print('first elementary squarefree product bypassing the 10^7 radical-pair cut:',limit)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('data_dir',nargs='?',type=Path,default=Path(__file__).parent);x=ap.parse_args()
 compact(x.data_dir);radical(x.data_dir)
