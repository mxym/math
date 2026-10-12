#!/usr/bin/env python3
from collections import deque
from itertools import combinations,product
import json,math
from pathlib import Path

F8=tuple((a,b) for a in (-1,0,1) for b in (-1,0,1) if (a,b)!=(0,0))
P=((0,1),(3,1),(3,-1))
QEND=14

def pf(n):
 out=[];p=2
 while p*p<=n:
  if n%p==0:
   out.append(p)
   while n%p==0:n//=p
  p=3 if p==2 else p+2
 if n>1:out.append(n)
 return out
def sf(n):return n==math.prod(pf(n))
def maxgens(q):
 out=[]
 for p in pf(q):
  if p==2:out.append((0,1))
  elif p==7:out += [(3,1),(3,-1)]
  elif p in (3,5,11,13):out.append((p,0))
  else:raise ValueError(p)
 return tuple(out)
def mul(x,y):
 a,b=x;c,d=y
 return (a*c+2*b*d,a*d+b*c)
def divisors14():
 out=[]
 for es in product(range(3),range(2),range(2)):
  if es==(0,0,0):continue
  z=(1,0)
  for p,e in zip(P,es):
   for _ in range(e):z=mul(z,p)
  out.append((es,z))
 assert len(out)==11
 return tuple(out)
def div(z,g):
 x,y=z;a,b=g;D=abs(a*a-2*b*b)
 return (a*x-2*b*y)%D==0 and (-b*x+a*y)%D==0
def allowed(z,gs):return all(not div(z,g) for g in gs)
def A(q,gs):return {(x,y) for x in range(q) for y in range(q) if allowed((x,y),gs)}
def edge(r,d,q):
 x=r[0]+d[0];y=r[1]+d[1];s=(x%q,y%q)
 return s,((x-s[0])//q,(y-s[1])//q)
def path(par,v):
 rev=[]
 while par[v] is not None:
  u,d=par[v];rev.append(d);v=u
 return list(reversed(rev))
def witness(q,gs):
 S=A(q,gs);h={}
 for root in sorted(S):
  if root in h:continue
  h[root]=(0,0);par={root:None};todo=deque([root])
  while todo:
   r=todo.popleft()
   for d in F8:
    s,k=edge(r,d,q)
    if s not in S:continue
    w=(h[r][0]+k[0],h[r][1]+k[1])
    if s not in h:h[s]=w;par[s]=(r,d);todo.append(s)
    elif h[s]!=w:
     ws=path(par,r)+[d]+[(-a,-b) for a,b in reversed(path(par,s))]
     dx=sum(a for a,b in ws);dy=sum(b for a,b in ws)
     assert dx%q==0 and dy%q==0 and (dx or dy)
     return {'root':list(root),'steps':[list(d) for d in ws],
             'voltage':[dx//q,dy//q],'allowed_residues':len(S)}
 raise RuntimeError((q,gs))

lower=[]
for q in [1]+[x for x in range(2,14) if sf(x)]:
 gs=maxgens(q)
 lower.append({'q':q,'rational_primes':pf(q),'generators':[list(g) for g in gs],
               'witness':witness(q,gs)})

success_pairs={(0,1),(0,2)}
failed_sub=[]
for k in range(3):
 for idx in combinations(range(3),k):
  if idx in success_pairs:continue
  gs=tuple(P[i] for i in idx)
  failed_sub.append({'indices':list(idx),'generators':[list(g) for g in gs],
                     'witness':witness(QEND,gs)})
D=divisors14(); reps=[]
for pair in sorted(success_pairs):
 for pos,j in enumerate(pair):
  other=P[pair[1-pos]]
  for es,a in D:
   if a==P[j]:continue
   if div(a,P[j]):
    gs=(other,a)
    reps.append({'success_pair':list(pair),'prime_index':j,'prime':list(P[j]),
                 'replacement_exponents':list(es),'replacement':list(a),
                 'generators':[list(g) for g in gs],
                 'witness':witness(QEND,gs)})
out={
 'schema':'mxym-math-002-v4-sqrt2-f8-period-endpoint-1',
 'order':'Z[sqrt(2)]','period_endpoint':14,
 'prime_generators':[list(x) for x in P],
 'lower_period_failures':lower,
 'divisor_ideals_14':[{'exponents':list(es),'generator':list(a)} for es,a in D],
 'successful_prime_pairs':[list(x) for x in sorted(success_pairs)],
 'failed_prime_subsets':failed_sub,
 'proper_subideal_replacements':reps,
 'positive_certificate':'../v3/certificates_v3/sqrt2_eight_steps.json'
}
target=Path(__file__).resolve().parent/'sqrt2_period_endpoint.json'
target.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
Ls=[len(x['witness']['steps']) for x in lower+failed_sub+reps]
print('lower',len(lower),'divisors',len(D),'failed subsets',len(failed_sub),'replacements',len(reps))
print('witnesses',len(Ls),'steps',sum(Ls),'max',max(Ls))
