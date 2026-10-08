#!/usr/bin/env python3
"""Deterministic certificate producer. Never imported by independent checker."""
from collections import deque
from itertools import product
from pathlib import Path
import json

F8=tuple((a,b) for a in (-1,0,1) for b in (-1,0,1) if a or b)
R=6
G=((0,1),(1,1),(1,-1))

def mul(x,y):
 a,b=x;c,d=y
 return a*c-2*b*d,a*d+b*c

def norm(g):return g[0]*g[0]+2*g[1]*g[1]

def divides(g,z):
 a,b=g;c,d=z;n=norm(g)
 return (a*c+2*b*d)%n==0 and (a*d-b*c)%n==0

def key(g):
 p=(1,0)
 for generator,k in zip(G,g):
  for _ in range(k):p=mul(p,generator)
 return p

FACTORS=sorted([p for p in product(range(3),range(2),range(2)) if any(p)])
BASE=((1,0,0),(0,1,0),(0,0,1),(2,0,0))

def components(gens):
 allowed={(a,b) for a in range(R) for b in range(R) if not any(divides(key(g),(a,b)) for g in gens)}
 seen=set();groups=[]
 for root in sorted(allowed):
  if root in seen:continue
  lift={root:root};queue=deque([root]);seen.add(root)
  while queue:
   residue=queue.popleft();a,b=lift[residue]
   for da,db in F8:
    y=a+da,b+db
    r=(y[0]%R,y[1]%R)
    if r not in allowed:continue
    if r in lift:
     if lift[r]!=y:raise ValueError('positive certificate has voltage')
    else:lift[r]=y;seen.add(r);queue.append(r)
  groups.append(sorted([list(p) for p in lift.values()]))
 return sorted(groups,key=lambda x:(len(x),x))

def path(parent,r):
 result=[]
 while parent[r] is not None:
  r,j=parent[r];result.append(j)
 return result[::-1]

def voltage(q,allowed):
 seen=set()
 reverse={i:F8.index((-s[0],-s[1])) for i,s in enumerate(F8)}
 for root in ((a,b) for a in range(q) for b in range(q) if allowed((a,b))):
  if root in seen:continue
  lift={root:root};parent={root:None};todo=deque([root]);seen.add(root)
  while todo:
   r=todo.popleft();a,b=lift[r]
   for j,(da,db) in enumerate(F8):
    y=a+da,b+db;v=(y[0]%q,y[1]%q)
    if not allowed(v):continue
    if v in lift:
     if lift[v]!=y:
      steps=path(parent,r)+[j]+[reverse[k] for k in reversed(path(parent,v))]
      return {'start':list(root),'steps':steps}
    else:
     lift[v]=y;parent[v]=r,j;todo.append(v);seen.add(v)
 raise ValueError('no voltage cycle')

if __name__=='__main__':
 triple=((2,0,0),(0,1,0),(0,0,1))
 bases=[((1,0,0),(0,1,0)),((1,0,0),(0,0,1)),triple]
 positive=[{'generators':[list(g) for g in basis], 'components':components(basis)} for basis in bases]
 omissions=[((1,0,0),(2,0,0)),((1,0,0),(0,1,0)),((1,0,0),(0,0,1)),((0,1,0),(0,0,1))]
 negative=[]
 for omitted in omissions:
  gens=[g for g in FACTORS if g not in omitted]
  cert=voltage(6,lambda z: not any(divides(key(g),z) for g in gens))
  negative.append({'omitted':[list(g) for g in omitted],**cert})
 lower=[{'q':q,**voltage(q,lambda z:__import__('math').gcd(z[0]*z[0]+2*z[1]*z[1],q)==1)} for q in range(1,6)]
 data={'positive':positive,'maximal_failures':negative,'lower_periods':lower}
 target=Path(__file__).with_name('certificate.json')
 target.write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
 print('wrote',target,'bytes',target.stat().st_size)
 print('positive component sizes',[[len(c) for c in x['components']] for x in positive])
 print('failure lengths',[len(x['steps']) for x in negative])
 print('lower failure lengths',[len(x['steps']) for x in lower])
