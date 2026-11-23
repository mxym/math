from itertools import combinations as co, permutations as perm, product
from collections import Counter
Q=tuple(range(1,5)); P=( ((1,2),(3,4)),((1,3),(2,4)),((1,4),(2,3)) )
L=[(5+2*i,6+2*i) for i in range(3)]
leaf=[(12+3*i,13+3*i,14+3*i) for i in range(3)]
Nr={(0,1):21,(0,2):22,(1,2):23}
n=lambda i,j:Nr[tuple(sorted((i,j)))]
E=[(24+3*i,25+3*i,26+3*i) for i in range(3)]
def edge(i,j):assert i!=j;return (min(i,j),max(i,j))
def make(edges):
 a=[0]*33
 for i,j in edges:a[i]|=1<<j;a[j]|=1<<i
 return a
def ok(a):
 for i in range(33):
  for j in range(i):
   if (a[i]&a[j]).bit_count()+((a[i]>>j)&1)>2:return False
 return True
def skeleton():
 e={edge(0,q) for q in Q}|{edge(11,1)}
 for i in range(3):
  for x,h in zip(L[i],P[i]):
   e.update(edge(x,q) for q in h)
  e.update(edge(s,q) for q,s in zip(Q[1:],leaf[i]))
 return e
S0=skeleton()
def local(i):
 j,k=[h for h in range(3) if h!=i]
 ni,nk=n(i,j),n(i,k); u,v,w=E[i]; N=(ni,nk,u,v,w)
 X,Y=L[i]; G={}
 for B,C,D in perm(leaf[i]):
  base=S0|{edge(B,X),edge(B,Y),edge(C,X),edge(D,Y)}
  for s,t in perm((ni,nk,u),2):
   pset={B:(ni,nk,u), C:(v,w,s), D:(v,w,t)}
   for A in co(N,3):
    ns={**pset,11:A}
    base2=base|{edge(p,v0) for p,V in ns.items() for v0 in V}
    # the exclusive negative pair v,w is interchangeable, canonicalize after chart.
    if w in A and v not in A:continue
    # fill the four present centers: each needs two extra negatives, avoiding missing-positive mismatch
    Cs=L[j]+L[k];opts=[list(co((nk,u,v,w),2))]*2+[list(co((ni,u,v,w),2))]*2
    deg=[4-sum(h in V for V in ns.values()) for h in N]
    if min(deg)<0 or not ok(make(base2)):continue
    def fill(h,deg,ed):
     if h==4:
      if any(deg):return
      a=make(ed)
      if not ok(a):return
      # encode redundant two-site sign data in a short tuple, align n_ij by true IDs
      tags={}
      for t1 in (j,k):
       kn=n(i,t1);other=3-i-t1
       ca=tuple(x for x in L[other] if a[kn]>>x&1)
       la=tuple(x for x in leaf[i] if a[kn]>>x&1)
       assert B in la
       tags[t1]=(ca,kn in A,tuple(x for x in la if x!=B))
      key=tuple(sorted(ed-S0))
      if v in A and w in A or v not in A and w not in A:
       sub=lambda h: w if h==v else v if h==w else h
       if tuple(sorted(edge(sub(h),sub(y)) for h,y in key))<key:return
      G[key]=(tags,B,a)
      return
     for x,y in opts[h]:
      p,q=N.index(x),N.index(y)
      if not deg[p] or not deg[q]:continue
      dd=deg[:];dd[p]-=1;dd[q]-=1
      if max(dd)>3-h:continue
      fill(h+1,dd,ed|{edge(Cs[h],x),edge(Cs[h],y)})
    fill(0,deg,base2)
 return [(e,*z) for e,z in G.items()]
def glue2(v1,i,v2,j):
 e,t,B,a=v1; f,T,C,b=v2
 ca,ep,ls=t[j];cb,et,rs=T[i]
 if ca!=cb or ep!=et or len(ls)!=len(rs):return
 nex=set()
 if ls:nex.add(edge(ls[0],rs[0]))
 eds=set(e)|set(f)|S0|nex
 if ok(make(eds)):return nex or True
def cores():
 g=[local(i) for i in range(3)]
 assert list(map(len,g))==[128,128,128]
 print('local',list(map(len,g)))
 compat={}
 for i,j in co(range(3),2):
  d={}
  for h,v in enumerate(g[i]):
   for k,w in enumerate(g[j]):
    e=glue2(v,i,w,j)
    if e is not None:d[h,k]=e
  compat[i,j]=d
  assert len(d)==880
  print('compat',i,j,len(d),flush=True)
 count=Counter()
 for (h,k),c in compat[0,1].items():
  for l,g2 in enumerate(g[2]):
   d=compat[0,2].get((h,l));f=compat[1,2].get((k,l))
   if not d or not f:continue
   count[0]+=1
   V=(g[0][h],g[1][k],g2)
   A=S0|set(V[0][0])|set(V[1][0])|set(V[2][0])
   for e in (c,d,f):
    if e!=True:A|=e
   a=make(A)
   if not ok(a):continue
   count[1]+=1
   yield V,A,count
 assert (count[0],count[1])==(84,30)
 print('joined',count[0],count[1])
def whole():
 count=Counter()
 Ts=[]
 for i in range(3):
  p={0,11}|set(leaf[i])|set(x for j in range(3) if j!=i for x in L[j])
  m=set(Q)|set(E[i])|{n(i,j) for j in range(3) if j!=i}
  Ts.append(tuple(1 if x in p else -1 if x in m else 0 for x in range(33)))
 for V,A,_ in cores():
  opts=[E[k] if V[i][1][j][1] else [-1] for k in range(3) for i,j in [tuple(v for v in range(3) if v!=k)]]
  for cs in product(*opts):
   edge1=set(A)
   for k,c in enumerate(cs):
    i,j=[v for v in range(3) if v!=k]
    if c>=0:edge1.add(edge(n(i,j),c))
   adj=make(edge1)
   if not ok(adj):continue
   count[0]+=1
   def margin(i,j):
    return tuple(sum(Ts[j][p] for p in range(33) if adj[h]>>p&1) for h in E[i])
   pairs=[(i,j) for i,j in co(range(3),2)]
   OO=[]
   for i,j in pairs:
    rows=margin(i,j);cols=margin(j,i)
    if any(x<0 or x>3 for x in rows+cols):break
    opt=[]
    for v in product(*(co(range(3),d) for d in rows)):
     if tuple(sum(q in ss for ss in v) for q in range(3))==cols:
      ed={edge(E[i][p],E[j][q]) for p,ss in enumerate(v) for q in ss}
      if ok(make(edge1|ed)):opt.append(ed)
    if not opt:break
    OO.append(opt)
   if len(OO)!=3:continue
   for cc in product(*OO):
    A0=make(edge1.union(*cc))
    if not ok(A0):continue
    count[1]+=1
    assert all(sum(T[p] for p in range(33) if A0[q]>>p&1)==-4*T[q] for T in Ts for q in range(33))
    yield A0,Ts
 assert count[0]==48 and count[1]==0
 print('residual',count[0],'complete',count[1])

if __name__=='__main__':
 assert not list(whole())
