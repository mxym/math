#!/usr/bin/env python3
"""Untrusted deterministic certificate producer (not an independent proof)."""
from collections import deque
from itertools import product
from math import gcd
from pathlib import Path
import json

F=tuple(sorted(set((a,b) for a in (-1,0,1) for b in (-1,0,1) if a or b)|{(-2,0),(2,0)}))
REV=tuple(F.index((-a,-b)) for a,b in F)
PRIMES=((0,1),(1,1),(1,-1))
DIVISORS=tuple(x for x in product(range(3),range(2),range(2)) if any(x))

def norm(z):return z[0]**2+2*z[1]**2

def multiply(x,y):
 a,b=x;c,d=y
 return a*c-2*b*d,a*d+b*c

def generator(exponents):
 result=(1,0)
 for g,e in zip(PRIMES,exponents):
  for _ in range(e):result=multiply(result,g)
 return result

def divides(g,z):
 a,b=g;c,d=z;n=norm(g)
 return (a*c+2*b*d)%n==0 and (a*d-b*c)%n==0

def primesieve(z):return gcd(norm(z),6)==1

def generic_partition():
 V={(a,b) for a in range(6) for b in range(6) if primesieve((a,b))}
 taken=set();groups=[]
 for root in sorted(V):
  if root in taken:continue
  lift={root:root};q=deque([root]);taken.add(root)
  while q:
   r=q.popleft();p=lift[r]
   for dx,dy in F:
    v=p[0]+dx,p[1]+dy;res=v[0]%6,v[1]%6
    if res not in V:continue
    if res in lift:
     if lift[res]!=v:raise ValueError('infinite')
    else:lift[res]=v;taken.add(res);q.append(res)
  groups.append(sorted(map(list,lift.values())))
 return groups

def exceptional_closure():
 E={tuple(v*sgn for v in g) for g in PRIMES for sgn in (-1,1)}
 C=set(E);queue=deque(E)
 while queue:
  p=queue.popleft()
  for dx,dy in F:
   z=p[0]+dx,p[1]+dy
   if z not in C and (z in E or primesieve(z)):
    C.add(z);queue.append(z)
 return sorted(map(list,C))

def previous_path(parents,z):
 ans=[]
 while parents[z] is not None:
  z,j=parents[z];ans.append(j)
 return ans[::-1]

def voltage(period,allowed):
 seen=set()
 for root in ((a,b) for a in range(period) for b in range(period) if allowed((a,b))):
  if root in seen:continue
  lift={root:root};parent={root:None};queue=deque([root]);seen.add(root)
  while queue:
   r=queue.popleft();p=lift[r]
   for j,(dx,dy) in enumerate(F):
    v=p[0]+dx,p[1]+dy;res=v[0]%period,v[1]%period
    if not allowed(res):continue
    if res in lift:
     if lift[res]!=v:
      steps=previous_path(parent,r)+[j]+[REV[i] for i in reversed(previous_path(parent,res))]
      return {'start':list(root),'steps':steps}
    else:lift[res]=v;parent[res]=r,j;queue.append(res);seen.add(res)
 raise ValueError('no voltage')

if __name__=='__main__':
 negatives=[]
 for removed in ((1,0,0),(0,1,0),(0,0,1)):
  other=[e for e in DIVISORS if e!=removed]
  w=voltage(6,lambda z:not any(divides(generator(e),z) for e in other))
  negatives.append({'missing':list(removed),**w})
 lower=[{'q':q,**voltage(q,lambda z:gcd(norm(z),q)==1)} for q in range(1,6)]
 data={'positive_components':generic_partition(),
       'exceptional_closure':exceptional_closure(),
       'maximal_failure_cycles':negatives,'lower_period_cycles':lower}
 target=Path(__file__).with_name('certificate.json')
 target.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
 print('positive',len(data['positive_components']),
       [len(x) for x in data['positive_components']],
       'closure',len(data['exceptional_closure']))
 print('negative lengths',[len(p['steps']) for p in negatives])
 print('lower lengths',[len(p['steps']) for p in lower])
 print('saved bytes',target.stat().st_size)
