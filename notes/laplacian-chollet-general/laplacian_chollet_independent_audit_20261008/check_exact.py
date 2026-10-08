"""Independent bounded diagnostic only, not a proof of universal assertions.
No imports from the candidate author's audit. Permanent uses Ryser inclusion-exclusion.
"""
from itertools import combinations
from fractions import Fraction
from math import prod
from pathlib import Path
import hashlib,json,random
ROOT=Path(__file__).resolve().parent
PROOF=ROOT.parent/'laplacian_chollet_general_20261008/proof_candidate.txt'

def permanent(a):
    n=len(a)
    if n==0:return 1
    answer=0
    for m in range(1,1<<n):
        term=prod(sum(row[j] for j in range(n) if m>>j&1) for row in a)
        answer+=(-1 if (n-m.bit_count())&1 else 1)*term
    return answer

def square(a):return [[z*z for z in row] for row in a]
def principal(a,m):
    s=[j for j in range(len(a)) if m>>j&1]
    return [[a[i][j] for j in s] for i in s]
def cycle(n):return [(i,(i+1)%n) for i in range(n)]
def theta(lengths):
    edges=[];n=2
    for l in lengths:
        path=[0]+list(range(n,n+l-1))+[1];n+=l-1
        edges.extend(zip(path,path[1:]))
    return n,edges

def connected(adj,omit=None):
    vertices=set(range(len(adj)))-({omit} if omit is not None else set())
    if not vertices:return True
    stack=[min(vertices)];seen=set(stack)
    while stack:
        v=stack.pop()
        for u in adj[v]&vertices-seen:seen.add(u);stack.append(u)
    return seen==vertices

cases=[('empty',0,[]),('isolated',1,[]),('edge',2,[(0,1)])]
for n in range(3,10):cases.append(('cycle_'+str(n),n,cycle(n)))
for lengths in [(1,2,2),(1,2,4),(2,2,3),(3,3,3),(2,3,4)]:
    n,e=theta(lengths);cases.append(('theta_'+str(lengths),n,e))
for n in [5,7,9]:cases.append(('chorded_cycle_'+str(n),n,cycle(n)+[(0,2)]))
cases.extend([
 ('two_triangles_cut_vertex',5,[(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),
 ('mixed_blocks_and_isolates',9,[(0,1),(1,2),(2,0),(2,3),(3,4),(4,5),(5,6),(6,3)]),
 ('subdivided_K4',7,[(0,4),(4,1),(0,5),(5,2),(0,6),(6,3),(1,2),(1,3),(2,3)]),
 ('K5',5,list(combinations(range(5),2))),
 ('K2_5',7,[(i,j) for i in [0,1] for j in range(2,7)])])

records=[];principal_checks=0;odd_checks=0;deficit_checks=0
for name,n,raw in cases:
    edges={tuple(sorted(e)) for e in raw};adj=[set() for _ in range(n)]
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    d=[len(s) for s in adj]
    a=[[d[i] if i==j else -int(j in adj[i]) for j in range(n)] for i in range(n)]
    min_gap=None
    for m in range(1<<n):
        b=principal(a,m);p=permanent(b);q=permanent(square(b));h=prod(b[i][i] for i in range(len(b)))
        assert q<=p*h<=p*p,(name,m,q,p,h)
        principal_checks+=1
        if m: min_gap=min(p*h-q,min_gap) if min_gap is not None else p*h-q
    noncycle_block=n>=3 and connected(adj) and all(connected(adj,v) for v in range(n)) and any(z!=2 for z in d)
    if noncycle_block:
        c={e:Fraction(1,d[e[0]]*d[e[1]]) for e in edges}
        for v in range(n):assert sum(Fraction(9,5)*z for e,z in c.items() if v in e)<=Fraction(9,10)
        for m in range(1<<n):
            size=m.bit_count();mass=sum(z for (u,v),z in c.items() if m>>u&1 and m>>v&1)
            if size>=2:
                exceptions=sum(1 for v in range(n) if m>>v&1 and (d[v]>=3 or any(not m>>u&1 for u in adj[v])))
                assert exceptions>=2,(name,m,exceptions)
                assert 4*mass<=size-Fraction(2,3),(name,m,mass)
                deficit_checks+=1
            if size&1:
                assert Fraction(9,5)*mass<=Fraction(size-1,2),(name,m,mass)
                odd_checks+=1
    records.append({'name':name,'vertices':n,'edges':sorted(edges),'all_principals':1<<n,'noncycle_block':noncycle_block,'minimum_nonempty_strong_gap':min_gap})

# Exact algebraic verification of the glue identities, including dimension-one,
# zero diagonal, zero row, negative off-diagonal, and singular PSD operands.
rng=random.Random(73190)
def gram(n):
    vectors=[[rng.randrange(-2,3) for _ in range(3)] for _ in range(n)]
    if n%2==0:vectors[0]=[0,0,0]
    return [[sum(x*y for x,y in zip(u,v)) for v in vectors] for u in vectors]
def glue(a,b):
    n,m=len(a),len(b);out=[[0]*(n+m-1) for _ in range(n+m-1)]
    for i in range(n):
        for j in range(n):out[i][j]+=a[i][j]
    f=[n-1]+list(range(n,n+m-1))
    for i in range(m):
        for j in range(m):out[f[i]][f[j]]+=b[i][j]
    return out

glue_checks=0
for n in range(1,5):
 for m in range(1,5):
  a=gram(n);b=gram(m);g=glue(a,b)
  av=a[-1][-1];bv=b[0][0];a0=[row[:-1] for row in a[:-1]];b0=[row[1:] for row in b[1:]]
  p1,p2,r1,r2=map(permanent,[a,b,a0,b0])
  q1,q2,t1,t2=map(lambda z:permanent(square(z)),[a,b,a0,b0])
  assert permanent(g)==p1*r2+r1*p2
  assert permanent(square(g))==q1*t2+t1*q2+2*av*bv*t1*t2
  glue_checks+=1

# Constants are exact rational comparisons, not floating-point approximations.
assert Fraction(8,5)-Fraction(19,12)==Fraction(1,60)
assert Fraction(2,9)-Fraction(3,16)-Fraction(2,64)==Fraction(1,288)
report={'status':'PASS: all bounded diagnostic assertions',
 'proof_sha256':hashlib.sha256(PROOF.read_bytes()).hexdigest(),
 'method':'Independent integer Ryser inclusion-exclusion; Fraction constraints; no candidate-audit import',
 'graph_cases':len(cases),'principal_checks':principal_checks,'odd_set_checks':odd_checks,
 'deficit_checks':deficit_checks,'glue_identity_pairs':glue_checks,'cases':records,
 'scope_limit':'These finite diagnostics are auxiliary only. Universal validity is assessed in the independent written audit.'}
(ROOT/'exact_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))
