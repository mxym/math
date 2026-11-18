import sys
from collections import Counter
import numpy as np
from orbits4 import canonical4
from sympl import lags

def ck(v,s):
 if not v:raise ArithmeticError(s)
def tab():
 # Pauli convention W_(a,b)=i^(parity(a&b)) X^a Z^b, sign conventions on L assembled from a basis.
 Ls=lags(4)
 ck(len(Ls)==2295,'L count')
 labels=[];signs=[]
 for L in Ls:
  elems=[0];exp=[0]
  for p in sorted(L):
   if p in elems:continue
   a=p&15;b=p>>4;phase=(a&b).bit_count()%2
   ee=[i^p for i in elems]
   ex=[(e+phase+2*((i>>4)&a).bit_count())%4 for i,e in zip(elems,exp)]
   elems+=ee;exp+=ex
  ck(len(elems)==16 and set(elems)==L|{0},'no loops')
  signs.append([1 if (e-((p&15)&(p>>4)).bit_count()%2)%4==0 else -1 for e,p in zip(exp,elems)])
  ck(all((e-((p&15)&(p>>4)).bit_count()%2)%2==0 for e,p in zip(exp,elems)),'real sign lift')
  labels.append(elems)
 return np.asarray(labels),np.asarray(signs)
def run():
 # Integer inverse Walsh transform of each stabilizer measurement; no diagonalization, numerical thresholds or LP.
 L,sg=tab(); H=np.asarray([[(-1)**((i&j).bit_count()%2) for j in range(16)] for i in range(16)])
 Slist=sum((canonical4(h) for h in range(5,9)),[])
 tally=Counter(); depths=Counter(); seen=set()
 for ell,line in enumerate(open(sys.argv[1] if len(sys.argv)>1 else 'phase4.survivors')):
  row,*codes=map(int,line.split());S=sorted(Slist[row]);h=len(S);ck(all(16<=q<=19 for q in codes),'all surviving phases unit')
  ck(len(codes)==h and (row,*codes) not in seen,'format/duplicate'); seen.add((row,*codes))
  d=dict(zip(S,[q-16 for q in codes]))
  r=[]
  for p in range(256):
   a,b=p&15,p>>4
   e=(a&b).bit_count()%2
   z=[(d[x]-d[x^a]+e+2*(x&b).bit_count())%4 for x in S if x^a in d]
   ck(z.count(1)==z.count(3),'Pauli real')
   r.append(z.count(0)-z.count(2))
  probs=(sg*np.asarray(r)[L])@H
  ck(np.min(probs)>=0 and np.all(np.sum(probs,axis=1)==16*h),'Born')
  flat=np.all((probs==0)|(probs==np.max(probs,axis=1)[:,None]),axis=1)
  # Each selected member must have support at least seed (minimum h).
  fl=L[flat & (np.sum(probs!=0,axis=1)>=h)].copy()
  rem=np.ones(256,dtype=bool);rem[0]=False;used=[]
  stage=None
  while rem.any():
   occ=np.bincount(fl.ravel(),minlength=256)
   zeros=np.flatnonzero(rem & (occ==0))
   if len(zeros):stage='uncovered';break
   one=np.flatnonzero(rem & (occ==1))
   if not len(one):stage='undecided';break
   needed=fl[np.any(fl==one[0],axis=1)][0]
   zz=needed[needed!=0]
   ck(np.all(rem[zz]),'forced disjoint')
   rem[zz]=False
   fl=fl[~np.isin(fl,zz).any(axis=1)]
   used.append(needed)
  if stage is None:stage='exact'
  ck(stage=='uncovered',('feasible or elimination inconclusive',row,ell,stage))
  depths[len(used)]+=1; tally[row]+=1
 ck([tally[i] for i in range(8)]==[1,4,4,16,16,64,56,64],'survivor counts')
 print('All 225 states admit no fractional cover; numbers by forced depth:',sorted(depths.items()))
if __name__=='__main__':run()
