"""Bounded exact audit for the written proof. No optimization libraries.
The proof does not depend on these finite checks.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json,hashlib,math
HERE=Path(__file__).resolve().parent

def connected(adj,omit=None):
 V=set(range(len(adj)))-({omit} if omit is not None else set())
 if not V:return True
 seen={min(V)};todo=list(seen)
 while todo:
  u=todo.pop()
  for v in adj[u]&V-seen:seen.add(v);todo.append(v)
 return seen==V

def two_connected(adj):
 return len(adj)>=3 and connected(adj) and all(connected(adj,i) for i in range(len(adj)))

def perm(A):
 n=len(A);p=[0]*(1<<n);p[0]=1
 for s in range(1,1<<n):
  i=s.bit_count()-1
  p[s]=sum(A[i][j]*p[s^(1<<j)] for j in range(n) if s>>j&1)
 return p[-1]

def check_graph(n,edges,principals=True):
 adj=[set() for _ in range(n)]
 for i,j in edges:adj[i].add(j);adj[j].add(i)
 d=list(map(len,adj));L=[[d[i] if i==j else -int(j in adj[i]) for j in range(n)] for i in range(n)]
 target_checks=0;poly_checks=0
 if principals:
  for bits in range(1<<n):
   S=[i for i in range(n) if bits>>i&1];A=[[L[i][j] for j in S] for i in S]
   P=perm(A);Q=perm([[x*x for x in row] for row in A]);z=math.prod(d[i] for i in S)
   assert 0<=Q<=P*z<=P*P,(n,edges,S,P,Q,z)
   target_checks+=1
 if two_connected(adj) and any(x!=2 for x in d):
  c={(i,j):F(1,d[i]*d[j]) for i,j in edges}
  x={e:F(9,5)*w for e,w in c.items()}
  for v in range(n):assert sum(w for e,w in x.items() if v in e)<=F(9,10)
  for bits in range(1<<n):
   S={i for i in range(n) if bits>>i&1};s=len(S)
   if s>=2:
    exceptional=[i for i in S if d[i]>=3 or not adj[i]<=S]
    assert len(exceptional)>=2
    mass=sum(w for e,w in c.items() if set(e)<=S)
    assert 4*mass<=F(s)-F(2,3)
   if s%2:
    mass=sum(w for e,w in x.items() if set(e)<=S)
    assert mass<=F(s-1,2)
    poly_checks+=1
 return target_checks,poly_checks

records=[];tot=[0,0]
for n in range(1,6):
 E=list(combinations(range(n),2))
 for mask in range(1<<len(E)):
  e=[E[j] for j in range(len(E)) if mask>>j&1]
  a,b=check_graph(n,e)
  tot[0]+=a;tot[1]+=b
 records.append({'all_labeled_graphs_order':n,'graph_count':1<<len(E)})

cases=[]
for n in [6,7,8,9]:cases.append(('cycle'+str(n),n,[(i,(i+1)%n) for i in range(n)]))
for n in [6,7]:cases.append(('complete'+str(n),n,list(combinations(range(n),2))))
cases += [('theta_1_2_3',5,[(0,1),(0,2),(2,1),(0,3),(3,4),(4,1)]),
 ('bowtie',5,[(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),
 ('triangle_bridge_cycle_and_isolated',8,[(0,1),(1,2),(2,0),(2,3),(3,4),(4,5),(5,6),(6,3)]),
 ('star',7,[(0,i) for i in range(1,7)])]
for name,n,e in cases:
 a,b=check_graph(n,e);tot[0]+=a;tot[1]+=b
 records.append({'case':name,'order':n,'edges':e,'principal_checks':a,'odd_polytope_checks':b})

report={'status':'all assertions passed',
 'purpose':'finite arithmetic audit only; not used by the proof',
 'proof_sha256':hashlib.sha256((HERE/'proof.txt').read_bytes()).hexdigest(),
 'principal_strong_and_chollet_checks':tot[0],
 'odd_matching_polytope_checks':tot[1],
 'cases':records}
(HERE/'diagnostics.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))
