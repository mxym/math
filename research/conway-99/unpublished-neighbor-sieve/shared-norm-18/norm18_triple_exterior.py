"""Exact exterior-incidence rejection of a uniform 38-site norm-18 seed triple.
Proof mode requires only Python 3.10+, NumPy and norm18_triple_core.py.
Run: python norm18_triple_exterior.py [chart IDs]
Optional certificate discovery: add --discover (requires SciPy).
"""
import base64, json, sys, zlib
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path
import numpy as np
from norm18_triple_core import core23, incidence, lab, nside, psd, reps, tables

def coreautos(p,fs):
 out=[]
 for perm in permutations(range(4)):
  centers=[lab.index(tuple(sorted(perm[a]for a in edge)))for edge in lab]
  try:
   groups=[p.index(tuple(sorted(centers[l]for l in g)))for g in p]
   leaves=[fs.index((groups[i],perm[q],centers[l]))for i,q,l in fs]
  except ValueError:continue
  move=[0]+[1+x for x in perm]+[5+x for x in centers]+[11+x for x in leaves]
  out.append((tuple(groups),tuple(move)))
 return out
def iso_code(A,aut):
 raw=A[23:,:23];R=[list(np.flatnonzero(r)) for r in raw]; allcodes=[]
 for groups,move in aut:
  re=sorted((groups[j//5],sum(1<<move[l]for l in r),23+j)for j,r in enumerate(R))
  order=[ind for role,mask,ind in re]
  sig=tuple(mask for role,mask,ind in re)+tuple(sum(int(A[order[5*i+k],order[5*j+l]])<<(5*k+l)for k in range(5)for l in range(5))for i,j in combinations(range(3),2))
  allcodes.append(sig)
 return min(allcodes)

def decode(target,code):
 p,fs=reps()[target][1];a,t=core23(p,fs);B=np.array([[(code[j]>>k)&1 for j in range(15)]for k in range(23)],dtype=int)
 X=np.zeros((15,15),int)
 for m,(i,j)in zip(code[15:],combinations(range(3),2)):
  for k in range(5):
   for l in range(5):
    X[5*i+k,5*j+l]=X[5*j+l,5*i+k]=m>>(5*k+l)&1
 return np.block([[a,B],[B.T,X]]),np.concatenate([t,-np.repeat(np.eye(3,dtype=int),5,axis=1)],axis=1)

def projected(A,t):
 # Unseen vertices: private negative groups of size five, and 61 common zero sites.
 F=12*np.eye(len(A),dtype=int)+2-A-A@A
 if np.min(F)<0:return False
 u=4*t+t@A
 if np.min(u)<0:return False
 d=14-A.sum(0)-u.sum(0)
 if np.min(d)<0:return False
 Y=305*F-61*(u.T@u)-5*np.outer(d,d)
 return psd(Y)
def search(target):
 _,(part,fs)=reps()[target];a,t=core23(part,fs);C=23
 codes=set();aut=coreautos(part,fs)
 roles=[]
 for i in range(3):
  g=[]
  for row in nside(part,fs,i):
   M=incidence(part,fs,i,row)
   ai=np.block([[a,M],[M.T,np.zeros((5,5),int)]])
   ti=np.concatenate([t,-(np.arange(3)==i).astype(int)[:,None]*np.ones((1,5),int)],axis=1)
   if projected(ai,ti):g.append((M,M@M.T,t@M))
  roles.append(g)
 basecap=12*np.eye(C,dtype=int)+2-a-a@a;st=[0]*6
 @lru_cache(None)
 def kands(i,j,idx,jdx):
  ri,rj=roles[i][idx],roles[j][jdx]
  kk=[]
  for table in tables(tuple(ri[2][j]),tuple(rj[2][i])):
   Sx=np.zeros((5,5),int)
   for h,inds in enumerate(table):Sx[h,list(inds)]=1
   # check pair common cap between C,Ni or Nj and Ni&Nj
   if np.any((ri[0].T@rj[0]+Sx)>2):continue
   if np.any(a@ri[0]+rj[0]@Sx.T+ri[0]>2)or np.any(a@rj[0]+ri[0]@Sx+rj[0]>2):continue
   Ai=np.block([[a,ri[0],rj[0]],[ri[0].T,np.zeros((5,5),int),Sx],[rj[0].T,Sx.T,np.zeros((5,5),int)]])
   ti=np.concatenate([t,-np.repeat((np.arange(3)==i)[:,None],5,axis=1).astype(int),-np.repeat((np.arange(3)==j)[:,None],5,axis=1).astype(int)],axis=1)
   if projected(Ai,ti):kk.append(Sx)

  return kk
 for ix in product(*(range(len(g)) for g in roles)):
  rr=[roles[k][u] for k,u in enumerate(ix)]
  st[0]+=1
  if np.min(basecap-rr[0][1]-rr[1][1]-rr[2][1])<0:continue
  ds=tuple(basecap[5+x,5+y]-sum(u[1][5+x,5+y]for u in rr) for x,y in part)
  if any(h>1 for h in ds):continue
  st[1]+=1
  B=np.concatenate([r[0]for r in rr],axis=1)
  if np.any((B.T@B-2)*(1-np.eye(15,dtype=int))>0):continue

  st[2]+=1
  ps=list(combinations(range(3),2));kinds=[]
  for i,j in ps: kinds.append(kands(i,j,ix[i],ix[j]))
  if any(len(g)==0 for g in kinds):continue
  st[3]+=1
  for pp in product(*kinds):
   X=np.zeros((15,15),int)
   for (i,j),u in zip(ps,pp):X[5*i:5*i+5,5*j:5*j+5]=u;X[5*j:5*j+5,5*i:5*i+5]=u.T
   A=np.block([[a,B],[B.T,X]])
   F=12*np.eye(38,dtype=int)+2-A-A@A
   if np.min(F)<0:continue
   st[4]+=1
   DD=14-A.sum(0);Y=61*F-np.outer(DD,DD)
   if psd(Y):
    st[5]+=1
    codes.add(iso_code(A,aut))
 return st,sorted(codes)


def words(A,t,F,site):
 # Exterior incidence columns. Nonadjacent sites have at most two common
 # neighbors; adjacent ones at most one. A zero entry of F forbids co-contacts.
 n=len(A);nn=[sum(1<<int(j) for j in np.flatnonzero(r))for r in A]
 pair=[sum(1<<j for j in range(n) if j!=i and F[i,j]>0)for i in range(n)]
 pos=[sum(1<<int(j) for j in np.flatnonzero(r>0))for r in t]
 neg=[sum(1<<int(j) for j in np.flatnonzero(r<0))for r in t]
 rows=[]
 def dfs(h,allow,one,two):
  if h.bit_count()>14:return
  if all((h&w).bit_count()==(h&v).bit_count() and (h&w).bit_count()<=3 for w,v in zip(pos,neg)):rows.append(h)
  while allow:
   lo=allow&-allow;allow-=lo;j=lo.bit_length()-1;N=nn[j]
   if two&lo or two&N or one&N&h:continue
   dfs(h|lo,allow&pair[j],one|N,two|(one&N))
 if site==-1:dfs(0,(1<<n)-1,0,0)
 else:dfs(1<<site,pair[site],nn[site],0)
 return rows
def system(A,t,F,site):
 n=len(A);rows=words(A,t,F,site)
 if site>=0:
  coords=[int(j)for j in np.flatnonzero(F[site])]
  H=np.array([[(w>>j)&1 for j in coords]for w in rows],dtype=np.int64).reshape(len(rows),len(coords))
  assert site in coords and F[site,site]>0
  return coords,H,F[site,coords],coords.index(site)
 W=np.array([[(r>>j)&1 for j in range(n)] for r in rows],dtype=np.int64)
 p,q=np.triu_indices(n,1)
 H=np.hstack([np.ones((len(W),1),dtype=np.int64),W, W[:,p]*W[:,q]])
 b=np.concatenate([[99-n],np.diag(F),F[p,q]])
 idx=np.flatnonzero(H.any(0)|(b!=0))
 return [int(j)for j in idx],H[:,idx],b[idx],0
def verifies(H,b,c):
 # Bound shell products before using fixed-width NumPy matrix multiplication.
 assert all(isinstance(x,(int,np.integer)) for x in c)
 assert sum(abs(int(x)) for x in c)*max(1,max(abs(int(x))for x in b))<2**62
 c=np.asarray(c,dtype=np.int64)
 return (not len(H) or int((H@c).min())>=0) and int(b@c)<0
def discover(A,t,cache):
 # SciPy only proposes integer potentials. No graph is rejected on its exit status.
 from scipy.optimize import linprog
 n=len(A);F=12*np.eye(n,dtype=np.int64)+2-A-A@A
 for site in [7,9,5,6,8,10,1,2,3,4,0]+list(range(11,n))+[-1]:
  coords,H,b,ic=system(A,t,F,site)
  for cert in cache.get(site,[]):
   c=[cert.get(j,0)for j in coords]
   if verifies(H,b,c):return [site,cert]
  if not len(H): c=[0]*len(coords);c[ic]=-1
  else:
   Z=linprog(b,A_ub=-H,b_ub=np.zeros(len(H)),bounds=(-1,1),method='highs')
   if not Z.success or Z.fun>=-1e-7:continue
   candidates=[]
   for mul in (1,2,3,4,5,6,7,8,10,12,24,60,120,10000,1000000):
    c=np.rint(mul*Z.x).astype(np.int64);c[ic]+=max(0,-int(min(H@c)))
    if verifies(H,b,c):candidates.append(c);break
   if not candidates:continue
   c=candidates[0]
  assert verifies(H,b,c)
  g=int(np.gcd.reduce(abs(np.asarray(c)))) or 1
  cert={j:int(x)//g for j,x in zip(coords,c)if x}
  cache.setdefault(site,[]).append(cert)
  return [site,cert]
 raise RuntimeError("No certified row or full incidence rejection on this core")
def verify(A,t,wit):
 site,dic=wit;site=int(site);dic={int(k):int(v)for k,v in dic.items()}
 F=12*np.eye(len(A),dtype=np.int64)+2-A-A@A
 coord,H,b,k=system(A,t,F,site)
 assert verifies(H,b,[dic.get(j,0)for j in coord])
def work(k,certs,generate):
 st,codes=search(k);cache={};wids={};wlist=[];refs=[]
 if not generate:
  assert k in certs and len(codes)==len(certs[k][1])
 for i,c in enumerate(codes):
  A,t=decode(k,c);assert iso_code(A,coreautos(*reps()[k][1]))==c
  if generate:
   w=discover(A,t,cache);key=(w[0],tuple(sorted(w[1].items())))
   if key not in wids:wids[key]=len(wlist);wlist.append(w)
   refs.append(wids[key])
  else: w=certs[k][0][certs[k][1][i]]
  verify(A,t,w)
 print("chart",k,*st,"orbits",len(codes),"certificates",len(wlist) if generate else len(certs[k][0]),flush=True)
 if generate:
  data=json.dumps([wlist,refs],separators=(',',':')).encode()
  print("DATA",k,base64.b64encode(zlib.compress(data,9)).decode(),flush=True)
if __name__=='__main__':
 generate='--discover' in sys.argv
 ids=[int(a) for a in sys.argv[1:] if a!='--discover'] or list(range(34))
 certs={} if generate else {int(k):json.loads(zlib.decompress(base64.b64decode(v))) for k,v in json.loads(Path(__file__).with_name('norm18_triple_exterior_certs.json').read_text()).items()}
 assert len(reps())==34
 for k in ids:assert 0<=k<34;work(k,certs,generate)
