from itertools import combinations,permutations,product
from collections import Counter
from functools import cache
def cells(s,q):
 v={}
 for m in reversed(range(16)):
  k=m.bit_count()
  total=99 if k==0 else 22 if k==1 else 8 if k==2 else (3+int((15^m).bit_length()<=s))if k==3 else q
  v[m]=total-sum(z for a,z in v.items()if m&a==m)
 return [v[j]for j in range(16)]
def stars(n,m):
 tg=[4*(not(m>>i&1))for i in range(4)];h=[0]*16
 pats=sorted((a for a in range(1,16)if a&m==0 and a.bit_count()>1 and n[a]),key=int.bit_count,reverse=True)
 def go(k,r):
  if k==len(pats):
   for i,z in enumerate(tg):h[1<<i]=z
   h[0]=r-sum(tg)
   if all(0<=x<=n[j]-(m==j)for j,x in enumerate(h)):yield h[:]
   return
  u=pats[k];b=[i for i in range(4)if u>>i&1]
  for z in range(1+min(r,n[u],min(tg[i]for i in b))):
   h[u]=z
   for i in b:tg[i]-=z
   yield from go(k+1,r-z)
   for i in b:tg[i]+=z
  h[u]=0
 yield from go(0,14)
def ren(m,p):return sum((m>>i&1)<<p[i]for i in range(4))
def verify(s,q,record):
 n=cells(s,q)
 if min(n)<0 or min(n[1<<j]for j in range(4))<7:return
 # only zeros in the union lie in singleton cells; exactly seven per singleton
 C=[(0,1,3),(0,0,n[0]-3)]
 for a in range(1,16):
  z=7 if a.bit_count()==1 else 0
  if z:C.append((a,0,z))
  if n[a]>z:C.append((a,-1,n[a]-z))
 assert sum(k for m,r,k in C if r<0)==25
 N=len(C);sz=[k for _,_,k in C]; ix={(a,b):j for j,(a,b,k)in enumerate(C)}
 pos=[(0,)]+[tuple(j for j,(m,r,sz) in enumerate(C)if r==-1 and m&(1<<i|1<<k)==0)for i,k in combinations(range(4),2)]
 assert all(sum(sz[x]for x in v)==3 for v in pos)
 msks=[tuple(i for i,(a,b,c) in enumerate(C)if a==j)for j in range(16)]
 gg=[[ix[ren(m,p),r]for m,r,sz in C]for p in permutations(range(4))if all(n[ren(m,p)]==n[m]for m in range(16))]
 # Form the invariant dual coefficients for all unsymmetrized literal cell columns.
 keys=[(0,i,0)for i in range(N)]+[(1,i,j)for i,j in combinations(range(N),2)]+[(2,i,j)for i in range(N)for j in range(i,N)]
 def keymap(z,p):
  k,i,j=z
  if k==0:return (0,p[i],0),1
  a,b=p[i],p[j];return (k,min(a,b),max(a,b)),(-1 if k==1 and a>b else 1)
 orbs=sorted({min(keymap(z,p)[0]for p in gg)for z in keys});ko={x:i for i,x in enumerate(orbs)}
 sparse,target=record;w=dict(sparse);edge=w.get(len(orbs),0);assert edge>=0
 wt={z:sum(w.get(ko.get(name,-1),0)*eps for name,eps in (keymap(z,p)for p in gg))for z in keys}
 rhs=sum(c*(sz[i]if k==0 else 0 if k==1 else 2*(2*sz[i]*sz[j]+12*sz[i]*(i==j)))for (k,i,j),c in wt.items())+14*edge
 assert rhs==target<0
 small=[(k,i,j,z)for (k,i,j),z in wt.items()if z];cnt=0
 for u,(m,role,_)in enumerate(C):
  for h in stars(n,m):
   # For C cell 0 split positive and zero, and each singleton into its two roles.
   opts=[]
   for j in range(16):
    ids=msks[j]
    if not ids:
     assert h[j]==0;continue
    if len(ids)==1:opts.append([((ids[0],h[j]),)]);continue
    l,r=ids;opts.append([((l,x),(r,h[j]-x))for x in range(max(0,h[j]-sz[r]+(r==u)),min(h[j],sz[l]-(l==u))+1)])
   for a in product(*opts):
    y=[0]*N
    for pairs in a:
     for j,v in pairs:y[j]=v
    if y[u]>=sz[u]:continue
    if sum(C[i][1]*v for i,v in enumerate(y))!=-4*role-4:continue
    if any(sum(y[i]for i in g)>1 for g in pos if u in g):continue
    if not matok(tuple(h)):continue
    coeff=edge*sum(sum(y[j]for j in g)for g in pos if u in g)
    for k,i,j,v in small:
     x=(int(u==i)if k==0 else (u==i)*y[j]-(u==j)*y[i] if k==1 else 2*y[i]*y[j]+(u==i)*y[j]+(u==j)*y[i])
     coeff+=v*x
    assert coeff>=0,(s,q,u,y,coeff)
    cnt+=1
 return cnt,rhs
@cache
def matok(h):
 i=next((i for i,v in enumerate(h)if v),None)
 if i==None:return True
 u=list(h);u[i]-=1
 for j,v in enumerate(u):
  if v>0 and not(i&j):
   u[j]-=1
   if matok(tuple(u)):return True
   u[j]+=1
 return False

W={"1":[[[0,19],[1,30],[2,14],[3,105],[4,46],[5,45],[6,70],[7,115],[8,68],[10,-25],[17,-87],[20,345],[23,168],[60,12],[61,-6],[62,-24],[63,35],[64,3],[66,97],[67,-1],[68,-64],[69,1],[70,11],[71,-21],[73,-6],[74,-27],[75,-2],[76,-12],[77,13],[78,-78],[80,-37],[81,-55],[82,-3],[83,59],[84,31],[85,5],[87,62],[88,10],[90,162],[92,81],[94,-108],[96,-7],[97,27],[98,-14],[103,60],[104,34],[105,67],[106,13],[108,7],[113,83],[115,-45],[118,90]],-2382],"2":[[[0,8],[1,10],[4,12],[5,2],[11,-65],[22,321],[23,-30],[26,-12],[27,-142],[28,85],[29,10],[83,17],[84,-15],[85,-40],[87,55],[88,49],[89,46],[91,83],[92,-118],[93,-47],[95,6],[96,-23],[97,-20],[98,9],[99,16],[100,8],[101,-9],[102,27],[103,11],[104,3],[105,9],[106,-58],[107,-35],[108,-10],[109,-9],[110,2],[113,3],[114,8],[115,4],[116,25],[117,59],[118,38],[119,69],[120,25],[121,84],[124,44],[127,4],[128,44],[131,3],[132,120],[133,-222],[134,-88],[137,-5],[138,4],[140,-6],[141,-30],[142,14],[149,-3],[154,1],[156,34],[157,-10],[160,-102],[161,-22],[162,5],[163,5]],-5184],"3":[[[1,3],[6,2],[10,-699],[15,-211],[19,-128],[21,-278],[22,-486],[24,-1633],[25,1040],[65,296],[66,-451],[67,-1371],[68,3675],[69,1238],[70,-492],[71,1208],[72,3758],[74,15],[75,-2],[77,-178],[78,-88],[79,37],[80,29],[82,199],[83,64],[84,344],[85,76],[87,-344],[88,187],[89,124],[90,-397],[91,81],[92,-374],[93,-830],[94,-307],[95,-224],[97,-76],[99,-222],[100,50],[104,751],[109,79],[110,-31],[112,164],[114,303],[115,-688],[116,-36],[118,-10],[122,76],[123,-902],[125,-20],[127,827],[128,247]],-86454],"4":[[[0,23],[1,60],[2,146],[3,120],[4,284],[5,140],[11,-703],[28,-1],[29,-110],[30,115],[31,1924],[32,-561],[33,8],[34,-5],[36,-448],[37,220],[38,130],[39,70],[40,197],[41,303],[44,-181],[46,407],[47,1050],[49,118],[50,-819],[53,1112],[55,-180]],-57144]}
for s in range(1,5):
 n,r=verify(s,s-1,W[str(s)]);print('s q stars rhs',s,s-1,n,r)
