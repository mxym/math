#!/usr/bin/env python3
"""Independent exact replay of the five seven-vertex graph exclusions. Standard library."""
import sys,itertools,math,json,zlib,base64,pathlib,hashlib,heapq
from fractions import Fraction as Q
def require(ok,msg):
 if not ok:raise ValueError(msg)
K=4096;den=4*K**4;F0=600;H=den*F0**2
E=list(itertools.combinations(range(7),2));eid={e:i for i,e in enumerate(E)}
def replay(data):
 mask=data['mask'];tar=data['target'];sym=data['sym'];masses=data['masses'];psd=data['psd'];tree=data['tree'];n=7
 require(tar==195650 and mask in (42232,44340,44404,44856,61112),'wrong target/class')
 isedge=[bool(mask>>i&1)for i in range(21)]
 # Take lexicographically maximal strong-then-weak ordered Gram entries under graph automorphisms.
 autos=[]
 for p in itertools.permutations(range(n)):
  m=tuple(eid[tuple(sorted((p[i],p[j])))]for i,j in E)
  if all(isedge[i]==isedge[j]for i,j in enumerate(m)):autos.append(m)
 valid=set()
 for i in sorted(range(21),key=lambda i:not isedge[i]):
  valid.update((i,p[i])for p in autos if p[i]!=i);autos=[p for p in autos if p[i]==i]
 require(len(sym)==len(valid)and set(map(tuple,sym))==valid,'orbit-order inequalities')
 for w in masses:require(len(w)==7 and sum(w)==F0 and all(type(x)is int and x>=0 for x in w),'probability weights')
 for v in psd:require(len(v)==7 and any(v)and all(type(x)is int for x in v),'Gram direction')
 def tighten(lo,hi):
  T=[[-K]*(2*n)for _ in range(2*n)]
  for i in range(2*n):T[i][i]=K
  for j,(a,b)in enumerate(E):
   T[a][b]=T[b][a]=T[n+a][n+b]=T[n+b][n+a]=lo[j]
   T[a][n+b]=T[n+b][a]=T[b][n+a]=T[n+a][b]=-hi[j]
  for i in range(2*n):
   row=T[i].copy()
   for a in range(2*n):
    for b in range(a):
     x,y=row[a],row[b]
     if x+y>=0:
      zz=(K*K-x*x)*(K*K-y*y);r=math.isqrt(zz);r+=r*r<zz
      t=(x*y-r)//K;T[a][b]=T[b][a]=max(T[a][b],t)
  lo=[T[a][b]for a,b in E];hi=[-T[a][n+b]for a,b in E]
  if any(T[a][n+a]>-K for a in range(n)):return None
  for _ in range(2):
   for i,j in sym:lo[i]=max(lo[i],lo[j]);hi[j]=min(hi[j],hi[i])
  return None if any(x>y for x,y in zip(lo,hi))else(lo,hi)
 # The producer used affine majorants. This verifier instead bounds the
 # combined univariate quartic directly, independently on every edge.
 def bern(w,v,l,h):
  def f(y):return w*(4*y**4-K*K*y*y)+v*y
  def fp(y):return w*(16*y**3-2*K*K*y)+v
  d=h-l;a=12*f(l);b=12*f(h)
  return [a,a+3*d*fp(l),a+6*d*fp(l)+d*d*w*(48*l*l-2*K*K),b-3*d*fp(h),b]
 def halves(u):
  l=[];r=[]
  while len(u)>1:
   l.append(u[0]);r.append(u[-1]);u=[(a+b+1)//2 for a,b in zip(u,u[1:])]
  return (l+u,u+r[::-1])
 maxsplit=0
 def checkdual(lo,hi,rows):
  nonlocal maxsplit
  wco=[0]*21;gco=[0]*21;gc=diag=tw=0
  for kind,idx,t in rows:
   t=int(t);require(t>0 and type(idx)is int and idx>=0,'dual multiplier')
   if kind==0:
    w=masses[idx];tw+=t;diag+=t*sum(c*c for c in w)
    for e,(i,j)in enumerate(E):wco[e]+=2*t*w[i]*w[j]
   elif kind==1:
    i,j=sym[idx];gco[i]+=t;gco[j]-=t
   else:
    require(kind==2,'test type');v=psd[idx];gc+=t*sum(x*x for x in v)
    for e,(i,j)in enumerate(E):gco[e]+=2*t*v[i]*v[j]
  const=12*(diag*(3*den//4)+gc*H);heaps=[];low=[];serial=0
  for w,v,l,h in zip(wco,gco,lo,hi):
   B=bern(w,v*(H//K),l,h);heaps.append([(-max(B),serial,B)]);serial+=1;low.append(max(B[0],B[-1]))
  # These lower references only choose a coordinate for subdivision; only the
  # upper coefficient bounds enter the accepting condition.
  for it in range(4096):
   ub=[-h[0][0]for h in heaps];total=const+sum(ub)
   if (total*10**6<=12*tar*tw*H)if tw else(total<0):
    maxsplit=max(maxsplit,it);return
   i=max(range(21),key=lambda j:ub[j]-low[j]);require(ub[i]>low[i],'false certificate')
   _,_,row=heapq.heappop(heaps[i])
   for B in halves(row):
    heapq.heappush(heaps[i],(-max(B),serial,B));serial+=1
    # Selection heuristic only: these lower references may round upward.
    low[i]=max(low[i],B[0],B[-1])
  raise ValueError('unresolved mixed quartic')
 pos=0;de=0;leaf=0
 def go(lo,hi,d):
  nonlocal pos,de,leaf
  require(pos<len(tree)and d<110,'truncated or unbounded certificate');cell=tree[pos];pos+=1;de=max(de,d);bounds=tighten(lo,hi)
  if cell==['X']:require(bounds is None,'invalid empty cell');return
  require(bounds is not None,'closure in a differently tightened cell');lo,hi=bounds
  if cell[0]=='D':
   checkdual(lo,hi,cell[1]);leaf+=1;return
  i,t=cell;require(type(i)is int and 0<=i<21 and type(t)is int and lo[i]<t<hi[i],'invalid split')
  z=hi.copy();z[i]=t;go(lo,z,d+1);z=lo.copy();z[i]=t;go(z,hi,d+1)
 go([-K if s else -K//2 for s in isedge],[-K//2 if s else K//2 for s in isedge],0)
 require(pos==len(tree),'unused tree nodes');print('PASS exact graph',mask,'nodes',pos,'dual leaves',leaf,'depth',de,'univariate refinements at most',maxsplit,flush=True)
if __name__=='__main__':
 path=pathlib.Path(__file__).with_name('kissing-six-noncycle-heptad-certificates.json')
 raw=path.read_bytes();require(hashlib.sha256(raw).hexdigest()=='3900b9d56a5d96a848600e96abe0c3c0c60b97d224ab7ea660f0cd4c81935b01','changed certificate snapshot')
 S=json.loads(raw)
 require(set(S)=={'42232','44340','44404','44856','61112'},'incomplete graph inventory')
 for k,z in S.items():
  if len(sys.argv)>1 and k not in sys.argv[1:]:continue
  d=json.loads(zlib.decompress(base64.b64decode(z)));require(d['mask']==int(k),'mislabelled graph');replay(d)
