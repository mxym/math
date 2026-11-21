#!/usr/bin/env python3
"""All-height S-unit center layer for at most one label >53. Needs checked public compact-core companion's table reader."""
from check_eac_sunits import P,walk,chk
from math import gcd,isqrt
from pathlib import Path
import sys
def smooth(z,alphabet):
 f=[];h=z
 for l in alphabet:
  while h%l==0:f.append(l);h//=l
 return h,f
def iroot(z,e):
 if e==2:return isqrt(z)
 a=1;b=1<<((z.bit_length()+e-1)//e)
 while b-a>1:
  c=(a+b)//2
  if c**e<=z:a=c
  else:b=c
 return b if b**e<=z else a
def prime(n):
 return n>1 and all(n%j for j in range(2,isqrt(n)+1))
def centers(path):
 allow={}
 for i,p in enumerate(P):
  for q in P[i+1:]:
   for h in range(2,q-p+1,2):
    g,r=divmod(q-p,h)
    if r==0 and g%2:allow.setdefault(h,[]).append((p,g))
 N=set()
 for a,b,c in walk(path,0):
  if c%2:
   h=b if a%2 else a
   for p,g in allow.get(h,()):N.add(p+g*c)
 chk(len(N)==36476 and max(N)==4020958408470,'centers')
 return N
def run(N,alphabet=P,large_min=59):
 stat=[0]*5;out=[]
 for n in sorted(N):
  E={};extra=[]
  for p in alphabet:
   if p>n-3 or n%p==0:continue
   h,f=smooth(n-p,alphabet)
   if h==1:
    if len(f)>=2:E[p]=set(f)
   else:
    e=1
    while large_min**e<=h:
     r=h if e==1 else iroot(h,e)
     if len(f)+e>=2 and r>=large_min and r**e==h and n-r>=3 and gcd(r,n)==1:
      extra.append((p,r,set(f)|{r}));stat[0]+=1
     e+=1
  for p,r,z in extra:
   h,f=smooth(n-r,alphabet)
   if h!=1 or len(f)<2:continue
   stat[1]+=1
   E[p]=z;E[r]=set(f)
   S={r};stack=[r];complete=True
   for x in stack:
    if x not in E:complete=False;break
    for y in E[x]-S:stack.append(y);S.add(y)
   if complete:
    stat[2]+=1
    # all reached vertices must reach r again
    R={r}
    while True:
     V=R|{x for x in S if E[x]&R}
     if V==R:break
     R=V
    if R==S:
     stat[3]+=1
     if prime(r):stat[4]+=1;out.append((n,tuple(sorted(R))))
   del E[p],E[r]
 return stat,out
if __name__=='__main__':
 path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).parent
 # A genuine EAC with exactly one label larger than the control alphabet.
 chk(run([2200],(3,5,7,11),13)[1]==[(2200,(3,13))],'genuine positive control')
 s,a=run(centers(path))
 print('centers 36476; candidate/smooth-r/closed/SCC/prime counts',s,'one-large cores',a)
 chk(s==[311308,14457,0,0,0] and not a,'unexpected one-large counts')
