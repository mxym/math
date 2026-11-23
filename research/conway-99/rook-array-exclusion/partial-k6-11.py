"""Exact 11-fiber P5 theorem for Conway's 99-graph problem. NumPy; SciPy for dual discovery in --orbits only.
Run without Python -O: assertions are part of the verifier."""
if not __debug__:raise RuntimeError("do not disable assertions")
from itertools import combinations,permutations,product
import numpy as np
import sys,time
from collections import Counter,defaultdict
P=np.array(list(permutations(range(3))),dtype=np.int8);I=np.array([list(map(tuple,P)).index(tuple(np.argsort(z)))for z in P],dtype=np.int8)
# comp[a,b] maps z -> a[b[z]]
comp=np.array([[list(map(tuple,P)).index(tuple(p[q]))for q in P]for p in P],dtype=np.int8)
def build(m):
 M=[frozenset((i,(i+1)%5))for i in range(m)];E=[frozenset(x)for x in combinations(range(6),2)if frozenset(x)not in M];n=len(E)
 G=[t for t in combinations(range(n),3)if len(set().union(*[E[i]for i in t]))==6];owner={tuple(sorted(q)):n+j for j,t in enumerate(G)for q in combinations(t,2)}
 H=[(i,n+j)for j,t in enumerate(G)for i in t]+[(i,j)for i,j in combinations(range(n),2)if not E[i]&E[j]and(i,j)not in owner]
 pa=list(range(n+len(G)));D={};free=0
 def root(i):
  while pa[i]!=i:i=pa[i]
  return i
 for i,j in H:
  ri,rj=root(i),root(j)
  if ri!=rj:pa[ri]=rj;D[i,j]=0;D[j,i]=0
  else:free+=1;D[i,j]=free;D[j,i]=-free
 assert len({root(i) for i in range(n+len(G))})==1
 assert (n,len(G),len(H),free)==(11,6,24,8)
 def path(i,j):
  def fg(i,j):
   q=tuple(sorted((i,j)))
   if q in owner:return (D[i,owner[q]],D[owner[q],j])
   return (D[i,j],)
  return tuple(v for v in fg(i,j)if v)
 pair=[(i,j,[k for k in range(n)if not(E[i]|E[j])&E[k]]) for i,j in combinations(range(n),2)if E[i]&E[j]]
 # batch evaluate composites from actual f-sites to g-sites.
 tests=[[(path(i,k)+path(k,j))for k in K]for i,j,K in pair if len(K)>=3]
 return M,E,G,H,free,path,tests,pair
def twists(m):
 M,E,G,H,v,path,tests,pairs=build(m);print('free',v,'core guards',len(tests),flush=True);cores=0;orbit=0;start=time.time();save=[]
 # fix up to simultaneous conjugacy (prefix chosen lex).
 conj=np.array([[comp[t,comp[p,I[t]]]for p in range(6)]for t in range(6)])
 tail=np.array(list(product(range(6),repeat=v-3)),dtype=np.int8).T
 sz=tail.shape[1]
 for pre in product(range(6),repeat=3):
  pis=sorted(set(tuple(t[list(pre)])for t in conj));
  if tuple(pre)!=pis[0]:continue
  mat=np.vstack([np.zeros(sz,dtype=np.int8),np.repeat(np.array(pre,dtype=np.int8)[:,None],sz,axis=1),tail]);cache={():mat[0]}
  def st(w):
   if w not in cache:
    zz=mat[abs(w[-1])]
    cache[w]=comp[zz if w[-1]>0 else I[zz],st(w[:-1])]
   return cache[w]
  ok=np.ones(sz,dtype=bool)
  for terms in tests:
   a,b,c=[st(w)for w in terms]
   for g in range(3):ok &= ~((P[a,g]==P[b,g])&(P[a,g]==P[c,g]))
  ids=np.flatnonzero(ok);cores+=len(ids)*len(pis)
  if len(ids) and len(save)<10:
   save.extend(tuple(map(int,z))for z in mat[1:,ids[:10]].T)
  if len(ids):
   for t in conj:
    if tuple(t[list(pre)])!=tuple(pre):continue
    A=t[tail];cond=np.ones(sz,dtype=bool);eq=cond.copy()
    for tt,rr in zip(tail,A):
     cond &= ~(eq&(tt>rr));eq &= tt==rr
    ok &= cond
   orbit+=np.count_nonzero(ok)
   for z in mat[1:,np.flatnonzero(ok)].T:
    yield tuple(map(int,z))
 assert (cores,orbit)==(117528,20416)
 print('m',m,'core survivors',cores,'conjugacy orbits',orbit,'time',time.time()-start,'samples',save[:3],flush=True)
def population_checks(M,E,G,W):
 n=len(E); S=[sum(1<<i for i in w) for w in W];grid=[sum(1<<i for i in t)for t in G]
 assert set(S)=={s for s in range(1<<n) if all((s&g).bit_count()==1 for g in grid)}
 assert all(any(not f&g and len(f|g|e)==6 for f,g in combinations(E,2))for e in M)
 # Connected nonbipartite abstract graph: adjacent degree equations p_a+p_b=18 determine p.
 seen={0}
 for _ in range(6):seen.update(k for f in E if seen&f for k in f)
 assert len(seen)==6 and any(all(frozenset(pair) in E for pair in combinations(t,2))for t in combinations(range(6),3))
 assert all(len(w)>=3 for w in W)  # binary population of each literal contact word

def balanced_anchor(f,star,M,E,W):
 # All possible exterior-class degrees of a core site in f, by two-walk equations to each fiber.
 n=len(E); C=np.array([[2 if a==b else int(not E[a]&E[b])for b in range(n)]for a in range(n)],dtype=int)
 rhs=np.array([16 if f==g else 5 if not E[f]&E[g] else 6 for g in range(n)])-C[f]@C
 U=np.array([[int(g in w)for w in W]for g in range(n)]);T=[]
 for a in range(6):
  b,c=next((b,c)for b,c in combinations(set(range(6))-{a},2)if all(frozenset(t)in E for t in ((a,b),(a,c),(b,c))))
  T.append(tuple(E.index(frozenset(t))for t in ((a,b),(a,c),(b,c))))
 vals=set()
 for v in product(range(4),repeat=len(M)):
  r=rhs-U[:,6:]@v;tw=[r[i]+r[j]-r[k]for i,j,k in T]
  if any(q<0 or q%2 for q in tw):continue
  h=tuple(q//2 for q in tw)+v
  if sum(h)==14-sum(C[f]) and np.array_equal(U@h,rhs) and all(not q or U[f,j] for j,q in enumerate(h)):vals.add(h[star])
 assert vals=={3}

def row_exists(R,b):
 # Binary exact equality feasibility. No optimization routine is used.
 while True:
  if np.any(b<0):return False
  cap=R.sum(axis=1)
  if np.any(cap<b):return False
  if not np.any(b):return True
  no=R[b==0].any(axis=0);yes=R[(b==cap)&(b>0)].any(axis=0)
  if np.any(no&yes):return False
  if not np.any(no|yes):break
  b=b-R[:,yes].sum(axis=1);R=R[:,~(no|yes)]
 r=min(np.flatnonzero(b>0),key=lambda i:int(cap[i]))
 i=np.flatnonzero(R[r])[0];keep=np.arange(R.shape[1])!=i
 return row_exists(R[:,keep],b) or row_exists(R[:,keep],b-R[:,i])

def study(mode):
 m=4
 if mode=='orbits':
  import scipy.sparse as sp,scipy.optimize as so
 M,E,G,H,v,path,tests,pairs=build(m);n=len(E);K=3*n
 p=[9]*6+[3]*m
 W=[[i for i,f in enumerate(E)if a in f]for a in range(6)]+[[i for i,f in enumerate(E)if not e&f]for e in M]
 population_checks(M,E,G,W)
 z0=[];keys=[]
 for j,w in enumerate(W):
  for t in product(range(3),repeat=len(w)):
   q=np.zeros(K,dtype=np.int8);q[[3*i+b for i,b in zip(w,t)]]=1;z0.append(q);keys.append(j)
 z0=np.array(z0,dtype=np.int8);keys=np.array(keys);ii,jj=np.triu_indices(K,1);idxi=np.arange(K)
 eye=np.eye(K,dtype=int);cnt=Counter();start=time.time()
 special=(3,0,4,4,3,3,3,4)
 for ig,tw in enumerate(twists(m) if mode=='orbits' else [special]):
  if mode=='orbits' and tw==special:cnt['reserved']+=1;continue
  A=np.zeros((K,K),dtype=np.int8);perm=(0,)+tw
  for i in range(n):A[3*i:3*i+3,3*i:3*i+3]=1-np.eye(3,dtype=np.int8)
  for i,j in combinations(range(n),2):
   if E[i]&E[j]:continue
   z=0
   for a in path(i,j):
    vv=perm[abs(a)];z=comp[vv if a>0 else I[vv],z]
   cc=3*i+np.arange(3);rr=3*j+P[z];A[cc,rr]=A[rr,cc]=1
  # residual outer common-neighbor capacity at each core pair
  B=12*eye+2-A-A@A
  assert B.min()>=0
  # sparse: zero entries ban cooccurrence. Actual one-outside-vertex/core-site common neighbor bound.
  bads=np.where((ii//3!=jj//3)&(B[ii,jj]==0))[0];valid=np.all(z0@A+z0<=2,axis=1)
  for k in bads:valid &= ~(z0[:,ii[k]]&z0[:,jj[k]]).astype(bool)
  Z=z0[valid];s=keys[valid];counts=np.bincount(s,minlength=len(p))
  if min(counts)==0:cnt['empty']+=1;continue
  # all target pairs with B>0 need coverage
  kk=np.flatnonzero((ii//3!=jj//3)&(B[ii,jj]>0));R=np.vstack([(s==i)for i in range(len(p))]+[Z.T,Z[:,ii[kk]].T*Z[:,jj[kk]].T])
  b=np.r_[p,B.diagonal(),B[ii[kk],jj[kk]]]
  if not R.any(axis=1).all():cnt['uncovered']+=1;continue
  if mode=='terminal':
   L=len(Z);tz={tuple(w):i for i,w in enumerate(Z.tolist())};shift=np.roll(Z.reshape((-1,n,3)),1,axis=2).reshape(Z.shape)
   sig=np.array([tz[tuple(z)]for z in shift.tolist()]);assert np.array_equal(sig[sig[sig]],np.arange(L))
   assert np.bincount(s).tolist()==[54,24,24,24,54,99,21,21,21,21]
   print('candidate sizes',np.bincount(s),[(i,sum(1 for j in range(len(E))if j in w))for i,w in enumerate(W)])
   cats=[]
   for j in range(6,6+m):
    e=M[j-6];r=next((x,y)for x,y in combinations(range(n),2)if not E[x]&E[y] and len(E[x]|E[y]|e)==6)
    cl=np.flatnonzero(s==j);nmat=Z[cl].copy();p1,p2=r;gs=[cl[nmat[:,3*p1+i]>0]for i in range(3)]
    h0=[];wpre=Z[:,ii[kk]]*Z[:,jj[kk]]
    for ids in product(*gs):
     zz=Z[list(ids)]
     if max(zz[0]@zz[1],zz[0]@zz[2],zz[1]@zz[2])>2:continue
     if np.any(wpre[list(ids)].sum(axis=0)>B[ii[kk],jj[kk]]):continue
     # Type e must cover all rung pairs of the prisms complementary to its missing edge.
     if any(len({int(np.argmax(z[3*x:3*x+3]))for z in zz})!=3 for x,y in combinations(range(n),2) if not E[x]&E[y]and len(E[x]|E[y]|e)==6):continue
     h0.append(tuple(sorted(ids)))
    h0=sorted(set(h0));cats.append(h0);print('e',tuple(e),'exact candidates',len(cl),'catalog size',len(h0),'cyclic',sum(tuple(sorted(sig[list(ids)]))==ids for ids in h0))
   assert list(map(len,cats))==[298,79,79,298]
   # Each ordinary 9-word class is solved for fixed special-word arrangements via a three-slice exact marginal operator.
   Zm=[sum(1<<int(i)for i in np.flatnonzero(z))for z in Z]
   conflict=[sum(1<<k for k,w in enumerate(Zm)if (v&w).bit_count()>=3)for v in Zm]
   allv=lambda ids:sum(1<<int(k)for k in ids)
   sc=[]
   for j in range(6):
    fw=W[j][:];anchor=next(f for f in fw if sum(1 for x,y in combinations(M,2)if not x&y and not (x|y)&E[f])==0)
    balanced_anchor(anchor,j,M,E,W)
    fw.remove(anchor);fw=[anchor]+fw
    a0=[k for k in range(len(Z))if s[k]==j];full=[(x,y,u,v)for x,y in combinations(fw,2)for u in range(3)for v in range(3)]
    BI=[int(B[3*x+u,3*y+v])for x,y,u,v in full];base=sum(zz<<(5*k)for k,zz in enumerate(BI));Aflag=sum(1<<(5*k)for k in range(len(BI)))
    codes=[sum((1<<(5*l))for l,(x,y,u,v)in enumerate(full)if z[3*x+u]and z[3*y+v])for z in Z]
    anchor_mask=[sum(31<<(5*k)for k,(x,y,a,b)in enumerate(full)if x==anchor and a==t)for t in range(3)]
    nonmask=sum(31<<(5*k)for k,(x,y,a,b)in enumerate(full)if x!=anchor)
    sliced=[];sis=[]
    for t in range(3):
     loc=[k for k in a0 if Z[k,3*anchor+t]];X={}
     for ids in combinations(loc,3):
      if any((Zm[a]&Zm[b]).bit_count()>=3 for a,b in combinations(ids,2)):continue
      sig0=sum(codes[k]for k in ids)
      if ((base+(Aflag*16)-sig0)&(Aflag*16))!=(Aflag*16):continue
      mask0=allv(ids);con=conflict[ids[0]]|conflict[ids[1]]|conflict[ids[2]]
      X.setdefault(sig0&anchor_mask[t],[]).append((sig0&nonmask,mask0,con))
     sliced.append(X);sis.append(sum(map(len,X.values())))
    impact=[i for i,e in enumerate(M)if len(set(fw)&set(W[6+i]))>=2];print('star',j,'slices',sis,'impact',impact,flush=True)
    tab=[]
    for cat in cats:
     tab.append([(sum(codes[k]for k in ids),int(conflict[ids[0]]|conflict[ids[1]]|conflict[ids[2]]))for ids in cat])
    sc.append((base,Aflag,nonmask,anchor_mask,sliced,impact,tab))
   from functools import lru_cache
   @lru_cache(maxsize=50000)
   def table(j,combs):
    base,flag,nmask,ams,sl,impact,tab=sc[j];a=0;ban=0
    for q,i in zip(impact,combs):
     z,c=tab[q][i];a+=z;ban|=c
    target=base-a
    if ((base+16*flag-a)&(16*flag))!=16*flag:return ()
    z=[[(h,x,c)for h,x,c in sl[g].get(target&ams[g],[])if not x&ban]for g in range(3)]
    if any(not zz for zz in z):return ()
    z.sort(key=len);lookup={}
    for k,x,c in z[2]:lookup.setdefault(k,[]).append(x)
    result=[];t2=target&nmask
    for k,x,c in z[0]:
     for h,y,d in z[1]:
      if c&y:continue
      for v in lookup.get(t2-k-h,()):
       if not (c|d)&v:result.append(x|y|v)
    return tuple(result)
   a1=[i for i in range(len(cats[1]))if table(3,(i,))];a2=[i for i in range(len(cats[2]))if table(1,(i,))]
   print('inner single filters',len(a1),len(a2),'cyclic',sum(tuple(sorted(sig[list(cats[1][i])]))==cats[1][i]for i in a1),flush=True)
   D=defaultdict(list)
   for i0,i3 in product(range(len(cats[0])),range(len(cats[3]))):
    if table(2,(i0,i3)):D[i0].append(i3)
   print('outer pair filter',sum(map(len,D.values())),'first catalogs',len(D),flush=True)
   assert (len(a1),len(a2),sum(map(len,D.values())))==(71,71,11978)
   ct0=Counter();seen_tables=set()
   for i1,i2 in product(a1,a2):
    a3=[i3 for i3 in range(len(cats[3]))if table(0,(i1,i2,i3))]
    a0=[i0 for i0 in D if table(4,(i0,i1,i2))]
    if a0 and a3:
     ct0['middle-pairs']+=1
     v3=set(a3)
     for i0 in a0:
      for i3 in D[i0]:
       if i3 not in v3:continue
       cidx=(i0,i1,i2,i3);cs=sum((list(cats[g][u])for g,u in enumerate(cidx)),[])
       if any((Zm[a]&Zm[b]).bit_count()>=3 for a,b in combinations(cs,2)):continue
       if not table(5,cidx):continue
       ctab=[table(t,tuple(cidx[q]for q in sc[t][5]))for t in range(6)]
       for cc in product(*ctab):
        bits=allv(cs)
        for o in cc:bits|=o
        inds=[i for i in range(len(Z))if bits>>i&1]
        if len(inds)!=66 or any(Zm[i]&Zm[k] and (Zm[i]&Zm[k]).bit_count()>=3 for i,k in combinations(inds,2)):continue
        obs=np.array([int(i in inds)for i in range(len(Z))])
        if not np.array_equal(R@obs,b):continue
        assert bits not in seen_tables;seen_tables.add(bits)
        ct0['code']+=1
        veto=False
        for root in inds:
         avail=[i for i in inds if i!=root and (Zm[i]&Zm[root]).bit_count()<=1]
         L0=np.vstack([Z[avail].T,np.ones(len(avail),dtype=int)])
         b0=np.r_[2-Z[root]-Z[root]@A,14-Z[root].sum()]
         if not row_exists(L0,b0):veto=True;break
        assert veto, 'contact table with no exterior row veto';ct0['row-rejected']+=1
        if np.array_equal(obs,obs[sig]):ct0['cyclic']+=1
        elif ct0['code']<10:print('ASYM genuine',cidx,flush=True)
   assert ct0=={'middle-pairs':67,'code':8,'cyclic':8,'row-rejected':8}
   print('Terminal exhaustive census:',dict(ct0),flush=True)

   continue
  Q3={}
  for iz,zw in enumerate(Z):
   for f in combinations(np.flatnonzero(zw),3):Q3.setdefault(f,[]).append(iz)
  qlist=[v for v in Q3.values()if len(v)>=2]
  def sparse(Q3):
   from scipy.sparse import coo_matrix
   a=[(i,j)for i,q in enumerate(Q3)for j in q]
   if not a:return coo_matrix((0,len(Z))).tocsr()
   ii0,jj0=zip(*a);return coo_matrix((np.ones(len(a)),(ii0,jj0)),shape=(len(Q3),len(Z))).tocsr()
  S=sparse(qlist)
  A0=R.astype(np.int16);S0=S.astype(np.int16).toarray()
  def dsolve(A,b,U,t,nodes,limit):
   nodes[0]+=1
   if nodes[0]>limit:return 'unknown'
   while True:
    if (b<0).any()or (t<0).any():return False
    cc=A.sum(axis=1);bad=(cc<b)
    if bad.any():return False
    if not np.any(b):return True
    no=A[b==0].any(axis=0)|U[t==0].any(axis=0);yes=A[(cc==b)&(b>0)].any(axis=0)
    if np.any(no & yes):return False
    if not np.any(no|yes):break
    b=b-A[:,yes].sum(axis=1);t=t-U[:,yes].sum(axis=1);keep=~(no|yes);A=A[:,keep];U=U[:,keep]
   # Branch on minimum choices for a required exact quota; force first allowed solution in that row
   valid=(cc>b)&(b>0);ks=np.flatnonzero(valid)
   if not len(ks):return True
   jj=min(ks,key=lambda k:(min(b[k],cc[k]-b[k]),cc[k]))
   poss=np.flatnonzero(A[jj]);ind=poss[np.argmax((A[:,poss]/(1+cc[:,None])).sum(axis=0))]
   keep=np.arange(A.shape[1])!=ind
   v=dsolve(A[:,keep],b-A[:,ind],U[:,keep],t-U[:,ind],nodes,limit)
   if v is True or v=='unknown':return v
   return dsolve(A[:,keep],b,U[:,keep],t,nodes,limit)
  def lpcheck(A0,b,S0,bs,depth=0):
   # All entries of A0,S0 nonnegative 0/1, every discovered contradiction checked with integer arithmetic.
   cnt['LP-calls']+=1
   while True:
    if np.any(b<0)or np.any(bs<0):return False
    total=A0.sum(axis=1)
    if np.any(total<b):return False
    if not np.any(b):return True
    no=A0[b==0].any(axis=0)|S0[bs==0].any(axis=0)
    yes=A0[(total==b)&(b>0)].any(axis=0)
    if np.any(no&yes):return False
    if not np.any(no|yes):break
    b=b-A0[:,yes].sum(axis=1);bs=bs-S0[:,yes].sum(axis=1);keep=~(no|yes);A0=A0[:,keep];S0=S0[:,keep]
   use=b>0;A0=A0[use];b=b[use];ubuse=S0.sum(axis=1)>bs;S0=S0[ubuse];bs=bs[ubuse];nq,lenx=A0.shape
   aeq=sp.hstack([A0,sp.eye(nq),-sp.eye(nq)],format='csr');aub=sp.hstack([S0,sp.csr_matrix((len(bs),2*nq))],format='csr')
   cv=np.r_[np.zeros(lenx),np.ones(2*nq)]
   r=so.linprog(cv,A_eq=aeq,b_eq=b,A_ub=aub,b_ub=bs,bounds=[(0,1)]*lenx+[(0,None)]*(2*nq),method='highs')
   assert r.success
   if r.fun>1e-8:
    for den in [1,10,100,1000,10000,1000000]:
     y=np.rint(den*r.eqlin.marginals).astype(np.int64);z=np.minimum(0,np.rint(den*r.ineqlin.marginals).astype(np.int64))
     # For any feasible binary x, yb+z bs <= (A^T y+S^T z)x <= sum_r max(0,r).
     # Python integers for all certificate multiplications and sums; no machine overflow.
     a=sum(int(t)*int(v)for t,v in zip(y,b))+sum(int(t)*int(v)for t,v in zip(z,bs))
     hi=sum(max(0,int(t))for t in y.astype(object)@A0+z.astype(object)@S0)
     if a>hi:
      cnt['VERIFIED-DUAL']+=1;return False
    raise RuntimeError('no verified dual')
   xx=r.x[:lenx];u=np.rint(xx).astype(int)
   if np.array_equal(A0@u,b)and np.all(S0@u<=bs):return True
   # Exact exhaustiveness: try both values, first 0 then 1.
   j=int(np.argmax(np.minimum(xx,1-xx)))
   keep=np.arange(lenx)!=j
   for val in (0,1):
    ok=lpcheck(A0[:,keep],b-val*A0[:,j],S0[:,keep],bs-val*S0[:,j],depth+1)
    if ok:return True
   return False
  nb=[0];ou=dsolve(A0,b,S0,np.ones(len(S0),dtype=np.int16),nb,12)
  cnt['DFS-nodes']+=nb[0]
  if ou=='unknown':
   ou=lpcheck(A0,b,S0,np.ones(len(S0),dtype=np.int16));cnt['LP-final']+=1
  cnt['PASS'if ou else 'REJECT']+=1
  assert not ou, ('unexpected contact code',ig,tw)
  if ig%4000==0:print('checked',m,ig,cnt,flush=True)

 if mode=='orbits':
  assert cnt['reserved']==1 and cnt['REJECT']+cnt['empty']+cnt['uncovered']==20415 and not cnt['PASS']
  print('Orbit proof:',dict(cnt),'seconds',round(time.time()-start,2),flush=True)
 else:
  assert cnt['empty']==cnt['uncovered']==0

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--stage',choices=['all','orbits','terminal'],default='all');args=ap.parse_args()
 if args.stage in ('all','orbits'): study('orbits')
 if args.stage in ('all','terminal'): study('terminal')
