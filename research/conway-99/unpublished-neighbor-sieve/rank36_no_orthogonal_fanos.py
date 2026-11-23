"""No orthogonal Fano pair at Seidel rank 36 in Conway's 99-graph.
All finite-field, capacity, and backtracking checks are integer arithmetic.
Runtime approximately 1.5 min with Python 3 and NumPy. Run in this directory.
"""
from two_fano_core import labeled, blocks, sides
from itertools import combinations, product
from collections import Counter
import numpy as np
N=labeled(15)
sq=(1,2,4)
def cap(i,j):return int(2-int(j in N[i])-len(N[i]&N[j]))
def options(j):
    X,Y=map(sorted,blocks[j:j+2])
    return [(x,y) for x in X for y in Y if cap(x,y)>0]
def tables():
    X,Y=map(sorted,blocks[2:4])
    rows=[]
    for x in X:
        rows.append([v for v in product(*(range(1+cap(x,y)) for y in Y)) if sum(v)==3])
    def rec(i,T,b):
        if i==5:
            assert b==(0,)*5
            yield T
            return
        for r in rows[i]:
            if any(a>u for a,u in zip(r,b)):continue
            yield from rec(i+1,T+[r],tuple(u-a for a,u in zip(r,b)))
    yield from rec(0,[],(3,)*5)
def piv(M):
    a=M.copy()%7;i=0;I=[]
    for j in range(a.shape[1]):
        ks=np.flatnonzero(a[i:,j])
        if not len(ks):continue
        k=i+ks[0];a[[k,i]]=a[[i,k]]
        a[i]=a[i]*pow(int(a[i,j]),-1,7)%7
        a[i+1:]=(a[i+1:]-a[i+1:,j,None]*a[i])%7
        I.append(j);i+=1
        if i==len(a):break
    return I
def inv(M):
    n=len(M);a=np.hstack((M.copy()%7,np.eye(n,dtype=int)));d=1
    for j in range(n):
        k=j+np.flatnonzero(a[j:,j])[0]
        if k!=j:a[[j,k]]=a[[k,j]];d=-d
        t=int(a[j,j]);d=d*t%7;a[j]=a[j]*pow(t,-1,7)%7
        coeff=a[:,j].copy();coeff[j]=0
        a=(a-coeff[:,None]*a[j])%7
    return d%7,a[:,n:]
def core():
    H=np.array([[3*int(x==y)-int(y in N[x])+4 for y in range(24)] for x in range(24)])
    U=np.array([[int(x in sides[j])-int(x in sides[j+1]) for x in range(24)] for j in [0,2]])
    return np.block([[H,U.T],[U,2*np.eye(2,dtype=int)]])
def first(T,d=2):
    X,Y=map(sorted,blocks[2:4])
    pairs=[(x,y) for i,x in enumerate(X) for j,y in enumerate(Y) for _ in range(T[i][j])]
    w=np.zeros((15,24+d),dtype=int);w[:,:24]=4
    for i,(x,y) in enumerate(pairs):w[i,[x,y]]-=1
    return w
def auts(flip):
 F,G=flip&1,flip>>1
 color=[tuple(i for i,s in enumerate(sides) if x in s) for x in range(24)]
 perms=[(i^F if i<2 else i^G) for i in range(4)]
 allowed=[set(v for v in range(24) if tuple(sorted(perms[i] for i in color[x]))==color[v] and len(N[x])==len(N[v])) for x in range(24)]
 def walk(f,rest,unused):
  if not rest:
   yield tuple(f[i] for i in range(24));return
  opts=[(len(q),i,q) for i in rest for q in [set(v for v in allowed[i]&unused if all((j in N[i])==(w in N[v]) for j,w in f.items()))]]
  _,i,q=min(opts,key=lambda t:t[0])
  for v in sorted(q):
   f[i]=v;yield from walk(f,rest-{i},unused-{v});del f[i]
 yield from walk({},set(range(24)),set(range(24)))
def action():
 X,Y=map(sorted,blocks[2:4]);maps=set()
 for flip in range(4):
  for p in auts(flip):
   im=[]
   for x,y in product(X,Y):
    a,b=p[x],p[y]
    if a not in X:a,b=b,a
    im.append(5*X.index(a)+Y.index(b))
   maps.add(tuple(im))
 return sorted(maps)
def reps():
 D=action();assert len(D)==4
 for T in tables():
  word=sum(T,())
  if all(tuple(word[j] for j in p)>=word for p in D):yield T
def basewords(d):
 p=options(0);tri=list(combinations(range(15),3))
 wf=np.zeros((len(p)*len(tri),39),dtype=np.int16)
 for i,(x,y) in enumerate(p):
  z=wf[i*len(tri):(i+1)*len(tri)]
  z[:,[x,y]]=1
  for j,t in enumerate(tri):z[j,[24+k for k in t]]=1
 raw=np.column_stack((4-wf[:,:24],np.zeros((len(wf),d),dtype=np.int16),4-wf[:,24:]))
 return raw,wf
def exact15(ok,v): # v integer 0/1 rows on 39 sites, needs 3 on each of final 15 sites
 n=len(ok)
 adj=[int.from_bytes(np.packbits(row,bitorder='little').tobytes(),'little')&~(1<<i) for i,row in enumerate(ok)]
 col=[int.from_bytes(np.packbits(row,bitorder="little").tobytes(),"little") for row in v.T if sum(row)]
 # all ten F exclusives (rows/cols of the second matrix) and all 15 ZF must have a triple
 if len(col)!=25:return False,0
 deg=[0]*25
 col_of=[tuple(k for k,c in enumerate(col) if (c>>i)&1) for i in range(n)]
 cnt=0
 def go(G,nsel):
  nonlocal cnt
  cnt+=1
  if nsel==15:return True
  if G.bit_count()<15-nsel:return False
  pick=0;best=10**9
  for j in range(25):
   u=3-deg[j]
   if u==0:continue
   a=(col[j]&G).bit_count()
   if a<u:return False
   if a-u<best:best=a-u;pick=j
  ss=G&col[pick]
  while ss:
   l=ss&-ss;ss^=l;i=l.bit_length()-1;G^=l
   G2=G&adj[i]
   for c in col_of[i]:
    deg[c]+=1
    if deg[c]==3:G2&=~col[c]
   ans=go(G2,nsel+1)
   for c in col_of[i]:deg[c]-=1
   if ans:return True
  return False
 return go((1<<n)-1,0),cnt
def main():
 d=0  # NO normalized Fano roots appended to the physical site lattice.
 H=core()[:24+d,:24+d];I=piv(H); _,R=inv(H[np.ix_(I,I)]);S=3*np.eye(15,dtype=int)+4
 wr,wf=basewords(d);res=Counter();res2=Counter()
 O=np.array([[int(j in N[i]) for j in range(24)] for i in range(24)],dtype=np.int16)
 mx=0;elo=0;allcharts=0
 for n,T in enumerate(reps()):
  allcharts+=1
  U=first(T,d);K=(S-U[:,I]@R@U[:,I].T)%7;J=piv(K)
  r=len(I)+len(J)
  if r>36:continue
  A=np.block([[H,U.T],[U,S]])
  I1=piv(A);e,U1=inv(A[np.ix_(I1,I1)])
  assert len(I1)==r
  if r==36 and e in sq:continue
  # nondegenerate complement always for d=0 or 1 at r36 as rank34 has e nonsquare.
  k=36-r;det=1 if e not in sq else 3 # ambient det nonsquare
  if k==2:assert det==1 # F7 two squares anisotropic
  # possible contacts must respect induced common-neighbor bounds with each known physical site
  edges=(4-U[:,:24]).astype(np.int16)
  near=np.block([[O,edges.T],[edges,np.zeros((15,15),dtype=np.int16)]])
  valid=np.all(wf@near<=2-wf,axis=1)
  w=wr[valid];v=wf[valid]
  A16=(A%7).astype(np.int16);R16=U1.astype(np.int16)
  p=w[:,I1]@R16%7
  J1=[j for j in range(len(A)) if j not in I1]
  use=np.all((p@A16[np.ix_(I1,J1)]-w[:,J1])%7==0,axis=1)
  w=w[use][:,I1];p=p[use];v=v[use]
  Sneed=-np.sum(w*p,axis=1)%7
  D=np.array(([1]*(k-1)+[det]) if k else [],dtype=np.int16)
  ys=np.array(list(product(range(7),repeat=k)),dtype=np.int16).reshape(7**k,k)
  norm=(ys*ys@np.array(D,dtype=np.int16))%7
  u,l=np.nonzero((Sneed[:,None]-norm[None,:])%7==0)
  y=ys[l];w=w[u];p=p[u];v=v[u]
  assert len(u)<4000 # memory sanity bound, not a feasibility cutoff
  if len(u):
   ok=(p@w.T+(y*D)@y.T)%7==4
   ok &= (v@v.T<=2)
   yes,nn=exact15(ok,v)
  else:yes,nn=False,0
  res[r,yes]+=1;res2[r,max(len(u),0)//50*50]+=1;mx=max(mx,nn);elo+=nn
  assert not yes
 print('orbit representatives:',allcharts)
 print('eligible rank and status:',sorted(res.items()))
 print('maximum and total DFS nodes:',mx,elo)
 assert allcharts==1357 and res=={(36,False):416,(35,False):269,(34,False):26}
 assert (mx,elo)==(25182,1626328)
if __name__=='__main__':main()
