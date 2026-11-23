"""Cube of eight triangle fibers is impossible in SRG(99,14,1,2).
Python 3.10+, NumPy 2.0+. Run with assertions enabled.
No solver or graph automorphism. Large row domains are completely omitted, never truncated."""
if not __debug__:raise RuntimeError('do not disable assertions')
from itertools import combinations,permutations,product
import numpy as np
import sys,time
from collections import Counter,defaultdict
P=np.array(list(permutations(range(3))),dtype=np.int8);I=np.array([list(map(tuple,P)).index(tuple(np.argsort(z)))for z in P],dtype=np.int8)
# comp[a,b] maps z -> a[b[z]]
comp=np.array([[list(map(tuple,P)).index(tuple(p[q]))for q in P]for p in P],dtype=np.int8)
def build(m):
 M=list(map(frozenset,[(0,1),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]));E=[frozenset(x)for x in combinations(range(6),2)if frozenset(x)not in M];n=len(E)
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
 assert (n,len(G),len(H),free)==(8,0,12,5)
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
 # Five free ternary maps; quotient only by simultaneous conjugacy here.
 M,E,G,H,v,path,tests,pairs=build(m);assert v==5 and not tests
 conj=[[int(comp[q,comp[x,I[q]]])for x in range(6)]for q in range(6)]
 vals=[z for z in product(range(6),repeat=5)if z==min(tuple(a[x]for x in z)for a in conj)]
 assert len(vals)==1393
 return vals
def reduced():
 raw=list(twists(7));R=np.array(raw,dtype=np.int8);nj=len(R)
 M,E,G,H,v,path,tests,pairs=build(7);n=len(E);N=n+len(G);q=len(H)
 parent=list(range(N));tree=[];ch=[]
 def rr(i):
  while i!=parent[i]:i=parent[i]
  return i
 for j,(x,y)in enumerate(H):
  a,b=rr(x),rr(y)
  if a!=b:parent[a]=b;tree.append(j)
  else:ch.append(j)
 base=np.zeros((q,nj),dtype=np.int8);base[ch]=R.T; maps={(u,v):(j,0)for j,(u,v)in enumerate(H)};maps.update({(v,u):(j,1)for j,(u,v)in enumerate(H)})
 weights=np.array([6**i for i in reversed(range(v))],dtype=np.int64)
 code=weights@R.T;mins=code.copy(); orbit=[]
 for a,b in [(0,1),(1,0)]:
  for h in permutations((2,3,4,5)):
   ff=(a,b)+h;tE=[E.index(frozenset(ff[i]for i in e))for e in E]
   t=tE+[n+G.index(tuple(sorted(tE[k]for k in g)))for g in G];phi=np.zeros_like(base)
   for j,(u,vv)in enumerate(H):
    k,iv=maps[t[u],t[vv]];phi[k]=I[base[j]] if iv else base[j]
   p={0:np.zeros(nj,dtype=np.int8)}
   while len(p)<N:
    old=len(p)
    for k in tree:
     i,j=H[k]
     if i in p and j not in p:p[j]=comp[phi[k],p[i]]
     elif j in p and i not in p:p[i]=comp[I[phi[k]],p[j]]
    assert len(p)>old
   assert all(np.all(comp[I[p[H[k][1]]],comp[phi[k],p[H[k][0]]]]==0)for k in tree)
   z=np.array([comp[I[p[H[k][1]]],comp[phi[k],p[H[k][0]]]]for k in ch])
   zz=np.minimum.reduce([weights@comp[t,comp[z,I[t]]]for t in range(6)]);mins=np.minimum(mins,zz);orbit.append(zz)
 buckets=defaultdict(set)
 for c,g in zip(mins,code):buckets[c].add(g)
 assert all(c==min(z)for c,z in buckets.items())
 for k,orb in enumerate(np.array(orbit).T):assert set(orb)==buckets[mins[k]]
 keep=R[code==mins].tolist()
 assert len(keep)==79 and Counter(map(len,buckets.values()))=={12:29,24:24,48:8,6:7,3:4,1:3,8:3,4:1}
 print('new distinct orbits',len(keep),Counter(map(len,buckets.values())),flush=True)
 return keep
def outer(ww,A,limit):
   K=len(A);L=len(ww);Z=np.array([[w>>i&1 for i in range(K)]for w in ww],dtype=int)
   qr=12*np.eye(K,dtype=int)+2-A-A@A
   assert np.array_equal(Z.T@Z,qr)
   import functools,math
   def bits(r):
    while r:q=r&-r;r-=q;yield q.bit_length()-1
   nm=np.array(2-Z-Z@A,dtype=int);valid=[]
   for i,w in enumerate(ww):
    ids=[j for j,v in enumerate(ww)if i!=j and (v&w).bit_count()<=1 and not any(not nm[i,k]or not nm[j,k]for k in bits(v&w))]
    valid.append(sum(1<<j for j in ids))
   c2=[sum(1<<j for j,v in enumerate(ww)if (v&w).bit_count()>=2)for w in ww];cv=[(1<<L)-1]+[sum(1<<j for j,w in enumerate(ww)if w>>i&1)for i in range(K)]
   @functools.lru_cache(maxsize=30000)
   def bm(pool):
    if not pool:return True
    k=(pool&-pool).bit_length()-1;rem=pool^(1<<k)
    return any(not ww[k]&ww[t] and bm(rem^(1<<t))for t in bits(rem&valid[k]))
   def rows(i):
    w=ww[i];dem=(14-w.bit_count(),)+tuple(map(int,nm[i]));blue=sum(1<<j for j,v in enumerate(ww)if not w&v);res=[]
    def dfs(pool,b,sel):
     if len(res)>limit:return
     if b[0]==0:
      if not any(b[1:]) and bm(sel&blue):res.append(sel)
      return
     yes=no=0;best=None
     for col,nv in enumerate(b):
      mm=pool&cv[col];nn=mm.bit_count()
      if nv<0 or nv>nn:return
      if nv==0:no|=mm
      elif nv==nn:yes|=mm
      elif col:
       key=math.comb(nn,nv)
       if best is None or key<best[0]:best=(key,mm)
     if not(yes or no):
      k=best[1]if best else pool;ii0=k&-k
      dfs(pool^ii0,b,sel);yes=ii0
     if yes&no:return
     dont=0
     for k in bits(yes):
      if yes&c2[k]&~(1<<k):return
      dont|=c2[k]
     dfs(pool&~(no|dont|yes),tuple(nv-(yes&col).bit_count()for nv,col in zip(b,cv)),sel|yes)
    dfs(valid[i],dem,0);return res
   order=sorted([i for i in range(L)if ww[i].bit_count()==4],key=lambda i:valid[i].bit_count())
   rowsall={}
   # If enumeration reaches limit+1, drop this entire root, including its pair constraints.
   # Every retained domain is complete; compatibility on this subset is necessary.
   for i in order:
    rs=rows(i)
    if not rs:return 'empty-row',0,0,0
    if len(rs)<=limit:rowsall[i]=rs
   lens={i:len(rs)for i,rs in rowsall.items()}
   caps=[[2-(x&y).bit_count()for y in ww]for x in ww]
   LO={j:np.array([v&((1<<64)-1)for v in vs],dtype=np.uint64)for j,vs in rowsall.items()}
   HI={j:np.array([v>>64 for v in vs],dtype=np.uint64)for j,vs in rowsall.items()}
   @functools.lru_cache(maxsize=200000)
   def compE(i,h,j):
    row=rowsall[i][h];edge=(row>>j)&1;quota=caps[i][j]-edge
    a=LO[j];b=HI[j]
    pick=(a>>(i%64))&1 if i<64 else (b>>(i-64))&1
    ok=(pick==edge)&(np.bitwise_count(a&np.uint64(row&((1<<64)-1)))+np.bitwise_count(b&np.uint64(row>>64))==quota)
    return int.from_bytes(np.packbits(ok,bitorder='little').tobytes(),'little')
   no=[0]
   def rec(dom,path):
    no[0]+=1
    if not dom:return path
    i=min(dom,key=lambda j:dom[j].bit_count())
    for h in bits(dom[i]):
     hd={}
     for j,v in dom.items():
      if i==j:continue
      x=v&compE(i,h,j)
      if not x:break
      hd[j]=x
     else:
      out=rec(hd,path+[(i,h)])
      if out is not False:return out
    return False
   out=rec({i:(1<<l)-1 for i,l in lens.items()},[])
   return ('ok' if out is not False else 'csp'),no[0],min(lens.values(),default=0),max(lens.values(),default=0)

def study(want=None):
 from functools import cache,lru_cache
 from time import perf_counter
 m=7
 M,E,G,H,v,path,tests,pairs=build(m);n=len(E);K=3*n
 f=lambda a,b:E.index(frozenset((a,b)))
 U=[[f(a,i)for i in range(2,6)]for a in (0,1)]
 W=[[i for i,e in enumerate(E)if a in e]for a in range(6)]+[[i for i,f0 in enumerate(E)if not e&f0]for e in M]
 ix=list(combinations(range(4),2))
 # Check the 13 allowed fiber supports directly: constant signed contact difference
 # and local matching constraint on all selected cross-rung pairs.
 clean=set()
 for b0 in range(1<<n):
  hit=lambda i:(b0>>i)&1
  if len({hit(U[0][i])-hit(U[1][i])for i in range(4)})>1:continue
  vs=[i for i in range(n)if hit(i)]
  if all(sum(not E[i]&E[j]for j in vs)<=1 for i in vs):clean.add(b0)
 assert clean=={sum(1<<i for i in w)for w in W} and len(clean)==13
 expected={17:4,24:39,37:2,53:4,65:4,66:4,70:2,76:50,77:42,78:9}
 ct=Counter();T0=perf_counter()
 def bits(w):
  while w:
   bit=w&-w;w^=bit;yield bit.bit_length()-1
 for ig,tw in enumerate(reduced()):
  if want and ig not in want:continue
  tt=perf_counter()
  A=np.zeros((K,K),dtype='int8');perm=(0,)+tuple(tw)
  for i in range(n):A[3*i:3*i+3,3*i:3*i+3]=1-np.eye(3,dtype=np.int8)
  for i,j in combinations(range(n),2):
   if E[i]&E[j]:continue
   z=0
   for a in path(i,j):
    vv=perm[abs(a)];z=comp[vv if a>0 else I[vv],z]
   cc=3*i+np.arange(3);rr=3*j+P[z];A[cc,rr]=A[rr,cc]=1
  B=12*np.eye(K,dtype=int)+2-A-A@A
  def valid(w):
   s=np.array(list(bits(w)),dtype=int)
   return (len(s)==0 or B[np.ix_(s,s)].min()>0) and all(int(A[s,k].sum())+int((w>>k)&1)<=2 for k in range(K))
  labs=[[(tuple(x),sum(1<<(3*f+i)for f,i in zip(fw,x)))for x in product(range(3),repeat=len(fw))]for fw in W]
  good={q for ls in labs for x,q in ls if valid(q)}
  bw=lambda w,q,g: (w>>(3*q+g))&1
  def rid(w,fs):return tuple(next(i for i in range(3)if bw(w,g,i))for g in fs)
  sets=[]
  for i,j in ix:
   r0=U[0][i];r1=U[1][j];s0=U[0][j];s1=U[1][i]
   pi0=list(map(int,A[3*r0:3*r0+3,3*r1:3*r1+3].argmax(axis=1)));pi1=list(map(int,A[3*s0:3*s0+3,3*s1:3*s1+3].argmax(axis=1)))
   opts=[]
   for pp in permutations(range(3)):
    cap=tuple(sum(1<<k for k in (3*r0+a,3*r1+pi0[a],3*s0+pp[a],3*s1+pi1[pp[a]]))for a in range(3))
    if not all(w in good for w in cap):continue
    vm=[]
    for fs in U:
     mm=B[np.ix_([3*fs[i]+a for a in range(3)],[3*fs[j]+a for a in range(3)])].copy()
     for w in cap:
      l,r=rid(w,[fs[i],fs[j]]);mm[l,r]-=1
     vm.append(tuple(mm.ravel()))
    if all(min(h)>=0 for h in vm):opts.append((cap,vm))
   sets.append(opts)
  starposs=[]
  for h in range(2):
   fs=U[h];star={x:w for x,w in labs[h]if w in good}
   # nine labeled-pair columns per nonanchor coordinate pair, base 16 to prevent carries.
   def code(q,x):return sum(1<<(4*(9*k+3*x[a-1]+x[b-1]))for k,(a,b)in enumerate(((1,2),(1,3),(2,3))))
   @lru_cache(maxsize=50000)
   def slice0(o,ta,tb,tc,star=star):
    zp=[sum(([k]*v for k,v in enumerate(h)),[])for h in (ta,tb,tc)]
    assert all(len(q)==3 for q in zp)
    opts=set()
    for b in set(permutations(zp[1])):
     for c in set(permutations(zp[2])):
      trip=tuple(sorted((o,a,y,z)for a,y,z in zip(zp[0],b,c)))
      if len(set(trip))!=3 or any(x not in star for x in trip):continue
      sites=tuple(star[x]for x in trip)
      if any((a&b).bit_count()>=3 for a,b in combinations(sites,2)):continue
      opts.add((sum(code(0,q[1:]) for q in trip),sites))
    return tuple(opts)
   @lru_cache(maxsize=50000)
   def starcode(spec,h=h,star=star,sl=slice0):
    ma,mb,mc,ta,tb,tc=(sets[i][k][1][h]for i,k in enumerate(spec))
    target=sum(int(x)<<(4*i)for i,x in enumerate(ta+tb+tc));ss=[]
    for o in range(3):
     z=sl(o,ma[3*o:3*o+3],mb[3*o:3*o+3],mc[3*o:3*o+3])
     if not z:return ()
     ss.append(z)
    ss.sort(key=len);d=defaultdict(list);sol=[]
    for u,z in ss[2]:d[u].append(z)
    for p,a in ss[0]:
     for q,b in ss[1]:
      if not target-p-q in d or any((i&j).bit_count()>=3 for i in a for j in b):continue
      for c in d[target-p-q]:
       if all((i&j).bit_count()<3 for i in a+b for j in c):sol.append(a+b+c)
    return tuple(sol)
   starposs.append(starcode)
  cnt=Counter()
  for spec in product(*(range(len(z))for z in sets)):
   caps=tuple(w for i,j in enumerate(spec)for w in sets[i][j][0]);light=[]
   for j in range(4):
    fs=[U[t][j]for t in (0,1)];d=Counter(rid(w,fs)for w in caps if any(bw(w,fs[0],k)for k in range(3)))
    if max(d.values())>2:break
    for (a,b),w in labs[j+2]:light.extend([w]*(2-d[a,b]))
   else:
    if any(w not in good for w in light):continue
    cnt['cap']+=1
    xx=starposs[0](spec)
    if not xx:continue
    yy=starposs[1](spec)
    if not yy:continue
    cnt['matched']+=1;cnt['tables']+=len(xx)*len(yy);cnt['max']=max(cnt['max'],len(xx)*len(yy))
    for x in xx:
     for y in yy:
      words=x+y+caps+tuple(light)+(0,0,0)
      assert len(words)==75 and all((a&b).bit_count()<=2 for a,b in combinations(words,2))
      veto,nodes,lo,hi=outer(words,A,limit=2500 if ig==17 else 400)
      assert veto in ('csp','empty-row'),('unrejected contact system',ig,spec)
      cnt[veto]+=1;cnt['cspnodes']+=nodes
  assert cnt['tables']==expected.get(ig,0)==cnt['csp']+cnt['empty-row']
  ct['cores']+=1;ct['tables']+=cnt['tables'];ct['empty-row']+=cnt['empty-row'];ct['csp']+=cnt['csp'];ct['cspnodes']+=cnt['cspnodes']
  if cnt['tables'] or ig%10==0:print(ig,tw,[len(z)for z in sets],dict(cnt),round(perf_counter()-tt,2),flush=True)
 print('TOTAL',dict(ct),round(perf_counter()-T0,2))
 if not want:assert ct['cores']==79 and ct['tables']==160 and ct['csp']==148 and ct['empty-row']==12
if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--case',type=int,choices=range(79));args=ap.parse_args()
 study(None if args.case is None else {args.case})
