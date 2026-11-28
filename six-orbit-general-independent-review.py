import json,gzip,base64,sys,hashlib,itertools
from collections import defaultdict,Counter
from functools import lru_cache
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form
class GSimple:
 def __init__(self,E=(),n=6):self.e=set(E);self.n=n
 def edges(self):return list(self.e)
 def degree(self,v=None):return [(j,self.degree(j))for j in range(self.n)] if v is None else sum(v in edge for edge in self.e)
 def __len__(self):return self.n
 def has_edge(self,a,b):return tuple(sorted((a,b)))in self.e
 def add_nodes_from(self,X):pass
 def add_edge(self,a,b):self.e.add(tuple(sorted((a,b))))
 def add_edges_from(self,X):self.e.update(X)
 def connect(self,a,b):
  vis={a}
  for k in range(self.n):vis|={y for x in vis for y in range(self.n) if self.has_edge(x,y)}
  return b in vis
def simple_supports():
 z=[()]
 for n in range(2,7):
  ed=list(combinations(range(n),2));ind={v:j for j,v in enumerate(ed)};P=[tuple(ind[tuple(sorted((p[a],p[b])))]for a,b in ed)for p in permutations(range(n))];all_seen=set();new=[]
  for old in z:
   for mask in range(1<<(n-1)):
    es=tuple(old)+tuple((i,n-1)for i in range(n-1)if mask>>i&1);code=sum(1<<ind[t]for t in es)
    if code in all_seen:continue
    all_seen.update(sum(1<<pm[ind[t]]for t in es)for pm in P);new.append(es)
  z=new
 assert len(z)==156
 return [GSimple(a)for a in z]
from itertools import combinations,permutations,product
B=json.loads(sys.argv[1]);tables={}
for chunk in B['reduced_gzip_base64']:
 t=json.loads(gzip.decompress(base64.b64decode(chunk)));assert not tables.keys()&t.keys();tables.update(t)
pairs=list(combinations(range(6),2));perms=list(permutations(range(6)));offset={x:i for i,x in enumerate(pairs)};pi=[list(p)+[6+offset[tuple(sorted((p[i],p[j])))] for i,j in pairs]for p in perms]
# Enumerate unlabeled connected support graphs from the external graph atlas, then link decorations up to its automorphisms. Orbit-stabilizer is an independent labeled total.
def atlas():
 U={};examples={}
 for G in simple_supports():
  if not all(G.connect(0,v)for v in range(6)):continue
  edges=sorted(tuple(sorted(e))for e in G.edges());a=list(G.degree());
  for k in range(4):
   for dou in combinations(edges,k):
    if len(set(v for e in dou for v in e))!=2*k:continue
    cross=[G.degree(i)+sum(i in e for e in dou)for i in range(6)]
    small=[i for i in range(6)if cross[i]<3]
    if any(G.has_edge(*e) for e in combinations(small,2)):continue
    for opt in product(*[[l for l in range(3)if l+c>=3 and (not l or c<3)]for c in cross]):
     ds=[x+y for x,y in zip(cross,opt)]
     if any(min(ds[i],ds[j])>3 for i,j in edges):continue
     m=tuple((e in edges)+(e in dou) for e in pairs);w=opt+m
     if any(w in oo for oo in [examples]):continue
     orbit={tuple(w[i] for i in mp)for mp in pi};code=''.join(map(str,min(orbit)))
     assert code not in U;U[code]=len(orbit)
     for v in orbit:examples[v]=code
 assert set(U)==set(tables)|{'000000001110111111000'}
 print('INDEPENDENT ATLAS',len(U),sum(U.values()),Counter(U.values()),flush=True)
atlas()
@lru_cache(None)
def col(R,n):
 if not R:return ()
 a=hermite_normal_form(Matrix(R).T);return tuple(tuple(int(a[i,j])for i in range(n))for j in range(a.cols))
def build(code):
 ds=list(map(int,code[:6]));m=list(map(int,code[6:]));n=sum(m)-5+sum(x>0 for x in ds);zero=(0,)*n
 def unit(pos,h=1):return tuple(h*int(i==pos)for i in range(n)) if pos>=0 else zero
 D=[];X=[];R=[];tree=GSimple();tree.add_nodes_from(range(6));r=0
 def edge(a,b,v,single=False):
  ix=len(D);D.append((a,b,v,ix if single else ix+1))
  if not single:D.append((b,a,tuple(-x for x in v),ix))
 for (a,b),mul in zip(pairs,m):
  for repeat in range(mul):
   if not tree.connect(a,b):i=-1;tree.add_edge(a,b)
   else:i=r;r+=1
   v=unit(i);edge(a,b,v)
   if repeat:X.append(tuple(c-d for c,d in zip(v,pre)))
   pre=v
 for a,l in enumerate(ds):
  if l:
   v=unit(r);edge(a,a,v,l==1)
   if l==1:R.append(unit(r,2));X.append(v)
   else:X.append(unit(r,2))
   r+=1
 assert r==n
 return n,zero,D,X,col(tuple(R),n)
def proof(code,tab):
 n,zero,arcs,nonzero,start=build(code)
 lib={col(tuple(map(tuple,json.loads(r))),n):w for r,w in tab.items()};assert len(lib)==len(tab)
 # Sympy column HNF pivots are the last nonzero row in the column.
 def has(K,v):
  a=list(v)
  for d in reversed(K):
   j=next(j for j in range(n-1,-1,-1)if d[j])
   q,r=divmod(a[j],d[j]);assert d[j]>0
   if r:return False
   a=[x-q*y for x,y in zip(a,d)]
  return not any(a)
 vis={};num=0
 def recur(k):
  nonlocal num
  if k in vis:return vis[k]
  assert not any(has(k,b)for b in nonzero)
  w=lib[k];num+=1;assert len(w)in (4,8,16);pos=zero;p=arcs[w[0]][0];hist=defaultdict(list);coll=set()
  for i,z in enumerate(w):
   a,b,x,rev=arcs[z];assert p==a and rev!=w[(i+1)%len(w)]
   for old in hist[p]:coll.add(tuple(h-o for h,o in zip(pos,old)))
   hist[p].append(pos);pos=tuple(c+d for c,d in zip(pos,x));p=b
  assert p==arcs[w[0]][0] and has(k,pos);children=set()
  for v in coll:
   assert not has(k,v);rr=col(k+(v,),n);assert rr!=k
   if not any(has(rr,x)for x in nonzero):children.add(rr)
  vis[k]=max([0]+[1+recur(r)for r in children]);return vis[k]
 depth=recur(start);assert set(vis)==set(lib);return num,depth
ret=[proof(k,t)for k,t in sorted(tables.items())];print('INDEPENDENT ROWS',len(ret),sum(x for x,y in ret),max(y for x,y in ret),flush=True)
ext={k:proof(k,t)for k,t in B['extra'].items()};print('FOUR EXTENSIONS',ext)
assert sorted(x for x,y in ext.values())==[7,10,19,43]
k='000000001110111111000';g=GSimple();g.add_nodes_from(range(6));g.add_edges_from([e for e,m in zip(pairs,k[6:]) if int(m)]);assert any(len(A)==3 and all(g.has_edge(x,y)==((x in A)!=(y in A))for x,y in pairs)for A in combinations(range(6),3))
e1=[z for z in ext if z[0]=='0'];assert sorted(sum(m1!=m2 for m1,m2 in zip(z,k))for z in e1)==[1,1]
assert sorted((k[i],z[i]) for z in e1 for i in range(len(z)) if k[i]!=z[i])==[('0','1'),('1','2')]
assert k[6:]==next(z[6:]for z in ext if z.startswith('1'))==next(z[6:]for z in ext if z.startswith('2'))
print('PASS STANDALONE',flush=True)
