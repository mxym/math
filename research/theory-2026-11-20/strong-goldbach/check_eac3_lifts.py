#!/usr/bin/env python3
"""Generate discrete-log rejection witnesses, then check each independently by group order and modular powers only."""
from itertools import permutations
from collections import Counter
from functools import lru_cache
from hashlib import sha256
P=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53)
D=10**50;T=200;E=140
def req(test,detail):
 if not test:raise ArithmeticError(detail)
def factors(v):
 out=set();i=2
 while i*i<=v:
  while v%i==0:v//=i;out.add(i)
  i+=1
 if v>1:out.add(v)
 return out
@lru_cache(None)
def order(p,q,a):
 """Independent of the lifting arithmetic: strip factors from Euler's phi."""
 h=p**a;o=(h//p)*(p-1)
 for s in sorted(factors(p-1)|{p}):
  while o%s==0 and pow(q,o//s,h)==1:o//=s
 req(pow(q,o,h)==1 and all(o%s or pow(q,o//s,h)!=1 for s in factors(p-1)|{p}),('order',p,q,a))
 return h,o
def verify(p,q,e,a,d):
 req(p in P and q in P and p!=q and 1<=e<=E and 1<=a<=T,'scope')
 h,o=order(p,q,a);tau=(-p-q*pow(p**e-1,-1,h))%h
 if d<0:
  req(pow(tau,o,h)!=1,('not outside',p,q,e,a))
 else:
  req(D<d<o and pow(q,d,h)==tau,('not out of range',p,q,e,a,d))
def generate(p,q):
 H=p**T; o=1
 while pow(q,o,p)!=1:o+=1
 steps=[];u=p;g=pow(q,o,H)
 for a in range(1,T):
  c=((g-1)//u)%p;inv=pow(q*c,-1,p) if c else None
  tab=[1]
  if c:
   for _ in range(1,p):tab.append(tab[-1]*g%H)
  steps.append((u,o,inv,tab));u*=p
  if c:o*=p;g=pow(g,p,H)
 for e in range(1,E+1):
  tau=(-p - q*pow(p**e-1,-1,H))%H
  d=1%steps[0][1];z=pow(q,d,H)
  for a,(u,o,inv,tab) in enumerate(steps,1):
   req((tau-z)%u==0,'generator invariant')
   digit=((tau-z)//u)%p
   if inv is None:
    if digit:yield (p,q,e,a+1,-1);break
   else:
    t=digit*inv%p;d+=t*o;z=z*tab[t]%H
    if d>D:yield (p,q,e,a+1,d);break
  else:raise ArithmeticError(('no rejection witness',p,q,e))
if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--write',help='optional output canonical witness table');ap.add_argument('--verify',help='read existing witness table instead of regenerating');args=ap.parse_args()
 f=open(args.write,'w') if args.write else None
 g=open(args.verify) if args.verify else None
 count=Counter();h=sha256();maxa=0
 for p,q in permutations(P,2):
  it=([int(z) for z in next(g).split()] for i in range(E)) if g else generate(p,q)
  for j,r in enumerate(it,1):
   pp,qq,e,a,d=r;req((pp,qq,e)==(p,q,j),'coverage');verify(*r)
   count['outside' if d<0 else 'oversize']+=1;maxa=max(a,maxa)
   s=' '.join(map(str,r))+'\n';h.update(s.encode())
   if f:f.write(s)
  req(j==E,'count')
 if g:req(not g.read().strip(),'extra lines');g.close()
 if f:f.close()
 req(sum(count.values())==29400,'total')
 print(dict(count),'total',sum(count.values()),'largest modulus exponent',maxa,'canonical ledger SHA256',h.hexdigest())
