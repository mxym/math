#!/usr/bin/env python3
"""Independent exact F3^4 size-18 spectral-set audit.
Requires Python >= 3.10, NumPy; no data files. Enumerates paired fibers,
then uses a forbidden-plane transversal bound followed by exact clique search.
No random sampling, float arithmetic, network, or optimization solvers.
"""
import numpy as np
from itertools import product,combinations
V=np.array(list(product(range(3),repeat=2)),dtype=np.int16)
W=np.array(list(product(range(3),repeat=4)),dtype=np.int16)
D=W[[next(iter(r[r!=0]),0)==1 for r in W]]
F=list(combinations(range(9),2))
P=V[np.array(F)]
A=np.array([np.concatenate((np.repeat([z],2,axis=0),p),axis=1) for z in V for p in P]).reshape(9,36,2,4)
mm=lambda t: np.array([t[...,2],t[...,3],t[...,2]**2,t[...,2]*t[...,3],t[...,3]**2,t[...,0]*t[...,2],t[...,0]*t[...,3],t[...,1]*t[...,2],t[...,1]*t[...,3]]).sum(axis=-1).transpose(1,2,0)%3
M=mm(A)
base=[0,3,1]
var=[8,2,6,4,7,5]
T=np.array(list(product(range(36),repeat=3)),dtype=np.int16)
mk=lambda ix: sum(M[q,T[:,k]] for k,q in enumerate(ix))
ml=mk(var[:3]);mr=mk(var[3:])
encode=lambda x:(x%3)@np.array([3**i for i in range(9)],dtype=np.int32)
rr=encode(mr);order=np.argsort(rr);ss=rr[order]
ff=A@D.T%3
bins=np.sum((ff==0)*32+(ff==2),axis=2)
vd=[(1,0),(0,1),(1,1)]
anchors=[F.index(tuple(sorted([np.where((V==v).all(axis=1))[0][0],np.where((V==(-np.array(v))%3).all(axis=1))[0][0]]))) for v in vd]
allMasks=set()
for typ in [(0,0,0),(0,0,1),(0,1,0),(0,1,1),(0,1,2)]:
 idx=[anchors[t] for t in typ]
 target=encode(-ml-M[base,idx].sum(axis=0))
 lo=np.searchsorted(ss,target);hi=np.searchsorted(ss,target,side='right');ns=hi-lo
 jj=np.repeat(np.arange(len(T)),ns);jk=order[np.repeat(lo-np.cumsum(ns)+ns,ns)+np.arange(len(jj))]
 vv=np.c_[T[jj],T[jk]]
 zz=np.zeros(len(vv),dtype=np.uint64)
 for j in range(40):
  vals=bins[base,idx,j].sum()+sum(bins[q,vv[:,k],j] for k,q in enumerate(var))
  zz|=(vals==198).astype(np.uint64)<<j
 z=set(map(int,zz)); z={m for m in z if m.bit_count()>=9}
 print(typ,len(zz),len(z),max(m.bit_count() for m in z),flush=True)
 allMasks|=z
print("UNION",len(allMasks),flush=True)
# exact difference obstruction: search for 5-clique in complement first (uniform translate bound)
diff=(W[:,None]-W[None,:])%3
ds=np.array([next((i for i,u in enumerate(D) if np.array_equal(x,u) or np.array_equal(x,2*u%3)),-1) for x in W])
Dij=ds[diff@np.array([27,9,3,1])]
# classify projective hole pairs by explicit linear plane provenance; any missing plane <=9
planeMasks=set()
for i in range(40):
 for j in range(i):
  plane=((aa*D[i]+bb*D[j])%3 for aa,bb in product(range(3),repeat=2) if (aa,bb)!=(0,0))
  planeMasks.add(sum(1<<k for k in {ds[x@np.array([27,9,3,1])].item() for x in plane}))
planeMasks=list(planeMasks)
rest=[m for m in allMasks if not any(m&p==0 for p in planeMasks)]
print("AFTER EMPTY PLANE RULE",len(rest),flush=True)
# exact backup use different branch, maximal independent-set partition upper bound via pigeon across 3-point line cosets
assert len(allMasks)==524760 and len(rest)==2740 and len(planeMasks)==130
n1=0
for mz in rest:
 z=int(mz)
 nz=[[ (p!=q and (z>>int(Dij[p,q]))&1) for q in range(81)] for p in range(81)]
 adj=[sum(1<<q for q,y in enumerate(row) if y) for row in nz]
 def has(B,k,G):
  if k==0:return True
  if B.bit_count()<k:return False
  # greedily cover with independent sets; reverse-color usual branch avoided:
  cover=B; cs=[]
  while cover and len(cs)<k:
   batch=0;t=cover
   while t:
    bit=t&-t;p=bit.bit_length()-1;batch|=bit;t&=~(G[p]|bit)
   cs.append(batch);cover&=~batch
  if len(cs)<k:return False
  # binary maximum-vertex pivot; removes without duplication
  while B.bit_count()>=k:
   bit=B&-B;p=bit.bit_length()-1;B-=bit
   if has(B&G[p],k-1,G):return True
  return False
 n1+=1
 assert not has(adj[0],17,adj),(z,n1)
print("PASS: exact residual graphs",n1,flush=True)
