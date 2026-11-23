# Exact 36-site exhaustion for the unique-dot-nine triple, standard library only.
from itertools import combinations as co, permutations as perm, product
from collections import Counter, defaultdict
from sys import argv
def edge(i,j):assert i!=j;return (min(i,j),max(i,j))
def make(edges):
 a=[0]*36
 for i,j in edges:a[i]|=1<<j;a[j]|=1<<i
 return a
def ok(a):
 for i in range(36):
  for j in range(i):
   if (a[i]&a[j]).bit_count()+((a[i]>>j)&1)>2:return False
 return True
def localok(edges):return ok(make(edges))
Q=tuple(range(1,5));P0=[((1,2),(3,4)),((1,3),(2,4)),((1,4),(2,3))]
P1=[((1,2),(1,3)),((1,4),(2,3)),((2,4),(3,4))]
L=[(5+2*i,6+2*i) for i in range(3)]
leaf=[(12,13,14),(15,16,17),(18,19,20,21)]
n=22; E=[(23,24,25,26),(27,28,29,30),(31,32,33,34,35)]
def setup(P):
 global S0,parents
 parents=[[q for es in P[i] for q in es] for i in range(3)]
 for i in [0,1]:parents[i].remove(1)
 parents=[sorted(x) for x in parents]
 e0={edge(0,q) for q in Q}|{edge(11,1)}
 for i in range(3):
  for x,h in zip(L[i],P[i]):e0.update(edge(x,q) for q in h)
  e0.update(edge(s,q) for q,s in zip(parents[i],leaf[i]))
 S0=e0
def endpoint(i):
 j=1-i; X,Y=L[i];u,v,w,z=E[i];N=(n,u,v,w,z);out=[]
 swaps=[dict(zip(N,(n,*U,*W))) for U in perm((u,v)) for W in perm((w,z))]
 for B,C,D in perm(leaf[i]):
  base=S0|{edge(B,X),edge(B,Y),edge(C,X),edge(D,Y)}
  for s,t in perm((n,u,v),2):
   for A in co(N,3):
    ns={B:(n,u,v),C:(w,z,s),D:(w,z,t),11:A}
    base2=base|{edge(p,v0) for p,V in ns.items() for v0 in V}
    deg=[4-sum(h in V for V in ns.values()) for h in N]
    if min(deg)<0 or not localok(base2):continue
    Cs=L[j]+L[2]; opts=[list(co(E[i],2))]*2+[list(co(N,2))]*2
    def fill(h,deg,ed):
     if h==4:
      if any(deg):return
      a=make(ed)
      if not ok(a):return
      key=tuple(sorted(ed-S0))
      for sw in swaps:
       if tuple(sorted(edge(sw.get(h,h),sw.get(y,y)) for h,y in key))<key:return
      ca=tuple(x for x in L[2] if a[n]>>x&1);la=tuple(x for x in (C,D) if a[n]>>x&1)
      sf=sum(bool(a[h]>>L[j][0]&a[h]>>L[j][1]&1) for h in E[i])
      out.append((key,(ca,n in A,la),B,sf))
      return
     for x,y in opts[h]:
      p,q=N.index(x),N.index(y)
      if not deg[p] or not deg[q]:continue
      dd=deg[:];dd[p]-=1;dd[q]-=1
      if max(dd)>3-h:continue
      fill(h+1,dd,ed|{edge(Cs[h],x),edge(Cs[h],y)})
    fill(0,deg,base2)
 return out
def endpoint_pairs():
 G=[endpoint(i) for i in [0,1]]
 print('single endpoint tables',len(G[0]),len(G[1]),flush=True)
 count=Counter()
 for e,(ca,v,ls),B,sf in G[0]:
  for f,(cb,w,rs),C,tf in G[1]:
   if ca!=cb or v!=w or len(ls)!=len(rs):continue
   ed=S0|set(e)|set(f)
   if ls:ed.add(edge(ls[0],rs[0]))
   if not localok(ed):continue
   count[0]+=1
   yield (e,f),ed,(B,C),(sf,tf)
 print('compatible endpoint tables',count[0],flush=True)
from functools import lru_cache
@lru_cache(None)
def table(r,c):
 if not r:return [()] if not any(c) else []
 if r[0]<0 or min(c)<0:return []
 return [ (w,)+v for w in co([i for i,a in enumerate(c) if a],r[0]) for v in table(r[1:],tuple(a-(i in w) for i,a in enumerate(c))) ]
def fields():
 T=[]
 for i in range(3):
  p={0}|set(leaf[i])|set(x for j in range(3) if j!=i for x in L[j])
  m=set(Q)|set(E[i])
  if i<2:p|={11};m|={n}
  T.append(tuple(1 if s in p else -1 if s in m else 0 for s in range(36)))
 return T
def paircore():
 T=fields()
 for V,ee,B,fs in endpoint_pairs():
  a=make(ee)
  def mg(i,j):return tuple(sum(T[j][p] for p in range(36) if a[s]>>p&1) for s in E[i])
  for w in table(mg(0,1),mg(1,0)):
   e=ee|{edge(E[0][p],E[1][q]) for p,v in enumerate(w) for q in v}
   A=make(e)
   if not ok(A):continue
   yield e,A,B,fs
def addsite(a,v,w):
 # exact against all existing sites assuming v has no existing neighbors except its Q parent already installed
 a=a[:]
 for h in range(36):
  if w>>h&1:a[h]|=1<<v
 a[v]|=w
 return a
def poschoices(a,B):
 candidates=[set(leaf[i])-{B[i]} for i in [0,1]]
 negidx=[sum(1<<y for y in E[i])|1<<n for i in range(2)]
 for p,v in zip(parents[2],leaf[2]):
  O=[]
  for lnum in (0,1,2):
   for Lx in co(L[2],lnum):
    for a0 in range(2):
     for c,d in product(*[[None]+list(sorted(g)) for g in candidates]):
      xy=[x for x in [c,d] if x is not None]
      base={p}|set(Lx)|set(xy)|({11} if a0 else set())
      g0=len(Lx)+a0+(c is not None)-1
      g1=len(Lx)+a0+(d is not None)-1
      if not(0<=g0<=1 and 0<=g1<=1):continue
      sels=list(product(E[0] if g0 else [-1],E[1] if g1 else [-1]))
      if g0 and g1:sels.append((n,-1))
      for h,k in sels:
       sites=base|{s for s in (h,k) if s>=0}
       mask=sum(1<<h0 for h0 in sites)
       if any((a[h0]&mask).bit_count()+(h0 in sites)>2 for h0 in range(36)):continue
       if any((a[h0]&a[h1]).bit_count()+(a[h0]>>h1&1)>=2 for h0,h1 in co(sites,2)):continue
       O.append((mask,g0,g1))
  yield O
def posa(e,a,B,fs):
 # clear trivial pending parent-leaf edges before feasibility checks
 aa=make(ed for ed in e if not (ed[0] in Q and ed[1] in leaf[2]))
 opts=list(poschoices(aa,B))
 neg=sum(1<<h for h in [n,*E[0],*E[1]])
 xa=[sum(1<<h for h in leaf[i]) for i in (0,1)]
 def go(k,a,V,co0,co1,repeated):
  if k==4:
   hc=[sum(m>>l&1 for m in V) for l in L[2]]
   if min(hc)<2 or sum(hc)>5:return
   ac=sum(m>>11&1 for m in V)
   if ac not in (1,2):return
   # All intra-2 sign-positive leaves have three private negs. Pair common-caps enforce earlier overlap≤1.
   if sum(hc)-4+1+(ac-1)+sum((m&xa[0]).bit_count() for m in V)>2:return
   if sum(hc)-4+1+(ac-1)+sum((m&xa[1]).bit_count() for m in V)>2:return
   A=a
   for v,w in zip(leaf[2],V):A=addsite(A,v,w)
   yield A,V
   return
  if sum(m>>11&1 for m in V)>2:return
  v=leaf[2][k]
  for mask,g,h in opts[k]:
   if co0+g>2 or co1+h>2 or mask&neg&repeated:continue
   if any((m&mask).bit_count()>1 for m in V):continue
   if k and parents[2][k]==parents[2][k-1] and mask<=V[-1]:continue
   if any(sum((m&xx).bit_count() for m in (*V,mask))>1 for xx in xa):continue
   if any(sum((m>>l)&1 for m in (*V,mask))+(3-k)<2 for l in L[2]):continue
   yield from go(k+1,a,V+(mask,),co0+g,co1+h,repeated|mask)
 yield from go(0,aa,(),0,0,0)
from functools import lru_cache
def schur(a,opts,T):
 I=[j for j in range(31) if j not in leaf[2]]
 MS=set(v for o in opts for v,_,_ in o)
 R={};J={};bad=set();candidates=sorted(MS);n=len(I)
 for sig in (0,1):
  rows=[]; masks={s:i for i,s in enumerate(candidates)};m=len(masks)
  def mat(i,j):
   if i<n and j<n:
    x,y=I[i],I[j]
    return 54*(x==y)-18*(a[x]>>y&1)+2-7*T[x]*T[y] if sig==0 else 44*(x==y)+11*(a[x]>>y&1)-2
   if i<n:
    x=I[i];s=candidates[j-n]
    return 2-18*(s>>x&1)-7*T[x] if sig==0 else 11*(s>>x&1)-2
   return 54*(i==j)-5 if sig==0 else 44*(i==j)-2
  for i in range(n+m):rows.append([mat(i,j) if j>=i else 0 for j in range(n+m)])
  prev=1
  for k in range(n):
   t=rows[k];p=t[k]
   if p<0 or (p==0 and any(t[k+1:n])):return lambda V:False
   if not p:
    bad.update(candidates[j] for j in range(m) if t[n+j]);continue
   for i in range(k+1,n+m):
    r=rows[i];u=t[i]
    for j in range(i,n+m):
     r[j],rem=divmod(r[j]*p-u*t[j],prev)
     if rem:assert (i>=n and candidates[i-n] in bad) or (j>=n and candidates[j-n] in bad)
   prev=p
  R[sig]=rows
  J[sig]={s:n+i for i,s in enumerate(candidates)}
 @lru_cache(None)
 def ok4(V):
  if any(w in bad for w in V):return False
  vs=sorted(V)
  for sig in (0,1):
   rr=R[sig];ii=[J[sig][w] for w in vs];M=[[rr[x][y] for y in ii] for x in ii];prev=1
   for k in range(len(M)):
    v=M[k];p=v[k]
    if p<0 or (p==0 and any(v[k+1:])):return False
    if not p:continue
    for i in range(k+1,len(M)):
     t=M[i];c=v[i]
     for j in range(i,len(M)):
      t[j],rem=divmod(p*t[j]-c*v[j],prev);assert not rem
    prev=p
  return True
 return ok4
def end36(A):
 T=fields(); n0=31
 Pm=[sum(1<<h for h in range(31) if t[h]==1)for t in T]
 Nm=[sum(1<<h for h in range(31) if t[h]==-1)for t in T]
 F=[[None if i==j else 2-(A[i]>>j&1)-(A[i]&A[j]).bit_count() for j in range(31)]for i in range(31)]
 H=[4*T[2][i]+(Pm[2]&A[i]).bit_count()-(Nm[2]&A[i]).bit_count() for i in range(31)]
 if min(H)<0 or max(H)>5:return
 used=[i for i in range(31) if H[i]]
 C=set(L[0]+L[1]+leaf[2]);rest=[i for i in used if i not in C]
 if any(T[2][i] for i in rest):return
 allow=[sum(1<<j for j in used if i!=j and F[i][j]>0) for i in range(31)]
 cones=[A[i]|(1<<i) for i in range(31)]
 def feasible(w,h):
  return all((w&cones[j]).bit_count()<=2 for j in range(31) if cones[j]>>h&1)
 def words(w,U):
  if all((w&p).bit_count()==(w&m).bit_count()<=3 for p,m in zip(Pm[:2],Nm[:2])):
   rr=(w&(Pm[0]&~Pm[1] | Nm[1]&~Nm[0])).bit_count()
   if rr<=3:yield w
  while U:
   bit=U&-U;U-=bit;j=bit.bit_length()-1
   ww=w|bit
   if feasible(ww,j):yield from words(ww,U&allow[j])
 R=[]
 for cc in co(sorted(C),4):
  if any(not H[j] for j in cc):continue
  w=sum(1<<j for j in cc)
  if any((w&allow[j]).bit_count()!=3 or not feasible(w,j) for j in cc):continue
  U=sum(1<<j for j in rest)
  for j in cc:U&=allow[j]
  R+=list(words(w,U))
 # cap incidence for the two endpoint omitted center pairs (all leftover witnesses accounted for).
 req={tuple(L[i]):F[L[i][0]][L[i][1]] for i in [0,1]}
 def complete(W):
  if any(sum((w>>j)&(w>>k)&1 for w in W)!=v for (j,k),v in req.items()):return
  a=A[:]
  for s,w in zip(E[2],W):a=addsite(a,s,w)
  if ok(a):yield a
 def go(h,U,W):
  if len(W)==5:
   if not any(h):yield from complete(W)
   return
  if any(t>5-len(W) for t in h):return
  zero=sum(1<<i for i,z in enumerate(h) if z==0)
  U=[r for r in U if not r&zero]
  by={i:[w for w in U if w>>i&1] for i in used if h[i]}
  if not by or any(len(rs)<h[i] for i,rs in by.items()):return
  from math import comb
  i=min(by,key=lambda j:comb(len(by[j]),h[j]))
  for S in co(by[i],h[i]):
   if any((w&y).bit_count()>2 for w,y in co(S,2)):continue
   H1=[t-sum(w>>j&1 for w in S) for j,t in enumerate(h)]
   if min(H1)<0:continue
   V=[w for w in U if not(w>>i&1) and all((w&y).bit_count()<=2 for y in S)]
   yield from go(H1,V,W+S)
 yield from go(H,R,())

def run(PP,case):
 setup(PP);T=fields()[2];cc=Counter()
 for idx,(e,a,B,_) in enumerate(paircore()):
  aa=make(ed for ed in e if not(ed[0] in Q and ed[1] in leaf[2]))
  pr=schur(aa,list(poschoices(aa,B)),T);cc[27]+=1
  for A,V in posa(e,a,B,None):
   cc[31]+=1
   if pr(V):
    cc['psd']+=1
    for _ in end36(A):cc['complete']+=1
 result=(cc[27],cc[31],cc['psd'],cc['complete'])
 print('pair cores, positive extensions, spectral survivors, full cores:',*result,flush=True)
 assert result==[(322,186824,602,0),(98,14192,0,0)][case]
if __name__=='__main__':
 for c in (list(map(int,argv[1:])) or [0,1]):
  assert c in (0,1);run((P0,P1)[c],c)
