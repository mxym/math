"""Rank-36 all-unit cap-boundary obstruction. Exact arithmetic and NumPy only."""
from itertools import combinations, permutations, product
import numpy as np
MATES = ((1,0,3,2),(2,3,0,1),(3,2,1,0))
IDENTITY = (0,1,2,3)
CERTIFICATES = {
    (MATES[0], MATES[0], MATES[0], (0,2,1,3)): {
        (0,9): (-1,-1,-1,1,-1,-1,1,1,0,-1,-1,1),
        (1,5): (-1,0,-1,1,-1,0,1,1,-1,-1,-1,1),
        (1,8): (0,-1,-1,1,-1,-1,1,1,-1,-1,-1,1),
        (2,10): (2,0,-2,-2,2,2,0,-2,2,0,-2,-2),
        (5,9): (-1,-1,-1,1,-1,0,1,1,-1,0,-1,1),
    },
    (MATES[0], MATES[0], MATES[1], IDENTITY): {
        (1,8): (0,-1,1,1,-1,-1,1,1,-1,-1,0,0),
        (2,11): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (3,10): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (5,8): (-1,-1,1,1,0,-1,1,1,-1,-1,0,0),
        (6,11): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (7,10): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (8,9): (-1,-1,1,1,-1,-1,1,1,-1,-1,0,0),
    },
}


def typegraph(p, q, r, return_map):
    graph = [set() for _ in range(12)]
    for i in range(4):
        for a,b in ((i,p[i]),(4+i,4+q[i]),(8+i,8+r[i]),
                    (i,4+i),(4+i,8+i),(8+i,return_map[i])):
            graph[a].add(b)
            graph[b].add(a)
    return graph


def connected(graph):
    reached = {0}
    pending = [0]
    while pending:
        new = graph[pending.pop()] - reached
        reached.update(new)
        pending.extend(new)
    return len(reached) == 12


def multiplicities(graph):
    return {(a,b): 2 - int(b in graph[a]) - len(graph[a] & graph[b]) - int(a//4 == b//4)
            for a,b in combinations(range(12),2)}


def code(parameters, ordered_wings=False):
    graph = typegraph(*parameters)
    keys = []
    for a,b,c in ((0,1,2),) if ordered_wings else permutations(range(3)):
        for order in permutations(range(4*a,4*a+4)):
            second = [next(j for j in graph[i] if j//4 == b) for i in order]
            third = [next(j for j in graph[i] if j//4 == c) for i in second]
            labels = list(order) + second + third
            keys.append(tuple(int(labels[j] in graph[labels[i]]) for i,j in combinations(range(12),2)))
    return min(keys)



inv7=np.array([0,1,4,5,2,3,6],np.int16)
def invmat(A):
 A=np.array(A,np.int16)%7;n,m=A.shape;B=np.eye(n,dtype=np.int16);piv=[];det=1
 for j in range(m):
  i=len(piv);ns=np.where(A[i:,j]!=0)[0]
  if not len(ns):continue
  ij=i+ns[0];piv.append(j);det=det*int(A[ij,j])*(-1 if ij!=i else 1)%7
  for X in (A,B):
   X[[i,ij]]=X[[ij,i]]
  s=inv7[A[i,j]]
  for X in (A,B):X[i]=X[i]*s%7
  coeff=A[:,j,None].copy();coeff[i]=0
  for X in (A,B):X[:]=(X-coeff*X[i])%7
 return piv,det,B

def make():
 U={};seen=set()
 for q,r,f in product(MATES,MATES,permutations(range(4))):
  pars=MATES[0],q,r,f;G=typegraph(*pars)
  if not connected(G) or min(multiplicities(G).values())<0:continue
  c=code(pars)
  if c in seen:continue
  seen.add(c)
  if c in {code(t) for t in CERTIFICATES}:continue
  L=3*np.eye(12,dtype=np.int16)-np.array([[int(j in G[i]) for j in range(12)] for i in range(12)],np.int16)
  pi,dt,_=invmat(L[:-1,:-1])
  if len(pi)==11:U[pars]=dt
 return U

def ordkey(G,perm):
 u,v,w=[perm.index(k) for k in range(3)];keys=[]
 for A in permutations(range(4*u,4*u+4)):
  B=[next(j for j in G[i] if j//4==v) for i in A];C=[next(j for j in G[i] if j//4==w) for i in B];sites=list(A)+B+C
  keys.append(tuple(int(sites[j] in G[sites[i]]) for i,j in combinations(range(12),2)))
 return min(keys)
def ordered():
 uns=make();cs={}
 for p,dt in uns.items():
  G=typegraph(*p)
  for w in permutations(range(3)):
   k=ordkey(G,w);cs.setdefault(k,(p,w,dt))
 return list(cs.values())

def startcase(components,wings,edge):
 DE=[];Q=[];R=[];SZ=[]
 for j,(NN,perm) in enumerate(zip(components,wings)):
  d=np.array([[int(t in NN[s]) for t in range(len(NN))] for s in range(len(NN))],np.int16)
  wr=np.array([perm[s//4] for s in range(len(NN))]);c=2-d-d@d-(wr[:,None]==wr[None,:])
  q=np.array([e for e in combinations(range(len(NN)),2) if c[e]>0 and (j>0 or any(a in e for a in edge))])
  DE.append(d);Q.append(q+12*j);R.append(wr);SZ.append(np.array([(wr[q]==k).sum(1) for k in range(3)]))
 D=np.zeros((36,36),np.int16)
 for j,d in enumerate(DE):D[j*12:j*12+12,j*12:j*12+12]=d
 Wg=np.concatenate(R);cap=2-D-D@D-(Wg[:,None]==Wg[None,:]);G=(3*np.eye(36,dtype=np.int16)-D+4)%7;I=invmat(G)[0];_,dt,inv=invmat(G[np.ix_(I,I)]);assert len(I)==34
 eps=1 if dt in (3,5,6) else 3
 ids=np.indices([len(q) for q in Q],dtype=np.int16).reshape(3,-1);ok=np.ones(ids.shape[1],bool)
 for k in range(3):ok &= (sum(SZ[j][k,ids[j]] for j in range(3))==2)
 ids=ids[:,ok];n=ids.shape[1];W=np.zeros((n,36),np.int16)
 for j in range(3):W[np.arange(n)[:,None],Q[j][ids[j]]]=1
 p=(4-W[:,I])%7;pr=p@inv%7;qn=(-(p*pr).sum(1))%7
 rows=2-W-W@D;r=np.array(list(product(range(7),repeat=2)),np.int16);hh=(r@np.diag([1,eps])@r.T%7).astype(np.int16);norm=np.diag(hh);qtab={}
 for qt in range(7):
  uv=np.where(norm==qt)[0];qtab[qt]=[uv[0]]+([uv[1]] if qt==0 and len(uv)>1 else [])
 ixseed=np.where(np.all(Q[0]==np.array(edge),1))[0][0];seeds=[(ww,k) for ww in np.where(ids[0]==ixseed)[0] for k in qtab[qn[ww]]]
 pairs=[];side=[];req=[]
 for j,e in enumerate(Q[0]):
  if j==ixseed:continue
  t=0 if edge[0] in e else 1;other=next(z for z in e if z!=edge[t])
  for z in range(cap[tuple(e)]):
   pairs.append(j);side.append(t);req.append((1-int(D[edge[t],other]),1-int(D[edge[t^1],other])))
 assert len(pairs)==18 and [side.count(j) for j in (0,1)]==[9,9]
 return locals()

def tables(C):
 W=C['W']; ids=C['ids'][0]; cap=C['cap']; rows=C['rows']; I=C['I'];pr=C['pr'];p=C['p']
 bins={i:np.where(ids==i)[0] for i in set(C['pairs'])};loc=np.zeros(len(W),np.int16);raw={}
 for i,v in bins.items():loc[v]=np.arange(len(v))
 masks=(W.astype(np.uint64)@(np.uint64(1)<<np.arange(36,dtype=np.uint64)))
 zero=((rows==0).astype(np.uint64)@(np.uint64(1)<<np.arange(36,dtype=np.uint64)))
 one=np.transpose(np.where(np.triu(cap==1,1)))
 pos=np.where(W)[1].reshape(-1,6);full=np.zeros((len(W),36),np.int16);full[:,I]=pr
 for i,u in bins.items():
  for j,v in bins.items():
   if j>i:continue
   G=(4*pr[u].sum(1)[:,None]-sum(full[np.ix_(u,k)] for k in pos[v].T))%7
   near=masks[u,None]&masks[v][None,:]
   bit=near&(near-np.uint64(1)); common2=(bit!=0)
   ok=(bit&(bit-np.uint64(1)))==0
   for l,k in one:
    uu=np.where(W[u,l]&W[u,k])[0];vv=np.where(W[v,l]&W[v,k])[0]
    if len(uu) and len(vv):ok[np.ix_(uu,vv)]=False
   ed=ok & (~common2) & ((zero[u,None]&masks[v][None,:])==0) & ((zero[v][None,:]&masks[u,None])==0)
   a=G.astype(np.uint8)+8*ok.astype(np.uint8)+16*ed.astype(np.uint8)
   raw[i,j]=a;raw[j,i]=a.T
 C['loc']=loc;C['table']=raw

def oneseed(C,seed,limit=None):
 W=C['W'];p=C['p'];pr=C['pr'];cap=C['cap'];ids=C['ids'];hh=C['hh'];norm=C['norm'];qn=C['qn'];order=C['pairs'];side=C['side'];req=C['req'];edge=C['edge'];rows=C['rows'];src,vec=seed
 source=(pr[src]@p.T)%7;nu=(4-source)%7;ok=(W@W[src]<=2)&(ids[0]!=C['ixseed'])
 for i,j in combinations(np.where(W[src])[0],2):
  if cap[i,j]==1:ok &= ((W[:,i]&W[:,j])==0)
 uz,fz=np.where(ok[:,None]&(qn[:,None]==norm[None,:])&(hh[vec][None,:]==nu[:,None]))
 qds=[np.where(ids[0,uz]==ind)[0] for ind in order];m=18
 if not all(map(len,qds)):return 0,1,0
 def bits(c):return int.from_bytes(np.packbits(c,bitorder='little').tobytes(),'little')
 mem={};cap1=[(a,b) for a,b in combinations(range(36),2) if cap[a,b]==1]
 def pair(i,j): # block arrays separate nonedges, edges
  a=qds[i];b=qds[j];u=uz[a];v=uz[b];F,G=fz[a],fz[b]
  info=C['table'][order[i],order[j]][np.ix_(C['loc'][u],C['loc'][v])]
  # Cast to signed F7 before subtracting; do not subtract in a byte.
  g=(info&7).astype(np.int16);J=(4-g-hh[np.ix_(F,G)])%7
  e=(J==1)&((info&16)!=0);n=(J==0)&((info&8)!=0)
  if order[i]==order[j]:
   keep=((u[:,None]<v[None,:]) if i<j else (u[:,None]>v[None,:]));n&=keep;e&=keep
  ty=int(side[i]!=side[j])
  if not req[i][ty] or not req[j][ty]:e[:]=0
  for y,k,N,E in ((i,j,n,e),(j,i,n.T,e.T)):
   mem[y,k]=([int.from_bytes(r.tobytes(),'little') for r in np.packbits(N,1,bitorder='little')],[int.from_bytes(r.tobytes(),'little') for r in np.packbits(E,1,bitorder='little')])
 def adj(i,l,j):
  if (i,j) not in mem:pair(i,j)
  a,b=mem[i,j];return a[l],b[l]
 ds=[(1<<len(a))-1 for a in qds];ns=0;control=None
 def go(rem,ds,hit,path):
  nonlocal ns,control
  ns+=1
  if not rem:control=path;return 1
  j=min(rem,key=lambda u:ds[u].bit_count());rest=rem-{j};z=ds[j]
  while z:
   bt=z&-z;z-=bt;l=bt.bit_length()-1;new=hit.copy();valid=True
   for o,v in path:
    _,ej=adj(o,v,j)
    if ej&bt:
     ch=1<<int(side[o]!=side[j])
     if (new[o]|new[j])&ch:valid=False;break
     new[o]|=ch;new[j]|=ch
   if not valid:continue
   d=ds.copy();h=path+[(j,l)]
   for k in rest:
    n,e=adj(j,l,k);ty=int(side[j]!=side[k]);d[k]&= n if new[j]&(1<<ty) else n|e
    for o,v in path:
     if hit[o]!=new[o] and new[o]&(1<<int(side[o]!=side[k])):d[k]&=adj(o,v,k)[0]
    if not d[k]:break
   else:
    if any(req[o][ty] and not(new[o]&(1<<ty)) and not any(side[k]==(side[o]^ty) and (d[k]&adj(o,v,k)[1]) for k in rest) for o,v in h for ty in (0,1)):continue
    t=go(rest,d,new,h)
    if t:return t
  return 0
 out=go(set(range(m)),ds,[0]*m,[])
 return out,ns,max(map(len,qds))

def group(G):
 aut=[]
 for P0 in permutations(range(4)):
  p=[0]*12
  for i,v in enumerate(P0):
   p[i]=v
   for j in G[i]:
    if j//4:p[j]=next(k for k in G[v] if k//4==j//4)
  if len(set(p))==12 and all(p[j] in G[p[i]] for i in range(12) for j in G[i]):aut.append(p)
 return aut
def seedreps(C,Gs,ps):
 from itertools import product
 # On the two other literal templates gauge their independent local point names. The anchor component's pair already fixed. No first/large role interchange.
 rs=[];can=[]
 for j in (1,2):
  U=group(Gs[j]);rs.append(len(U));can.append({tuple(s):min(tuple(sorted(p[z] for z in s)) for p in U) for s in combinations(range(12),2)})
 seen=set();out=[]
 for s,J in C['seeds']:
  pair=[tuple(np.nonzero(C['W'][s,12*j:12*j+12])[0]) for j in (1,2)]
  tag=(can[0][pair[0]],can[1][pair[1]])
  if ps[1]==ps[2]:tag=tuple(sorted(tag))
  k=(tag,int(C['qn'][s]),bool(J))
  if k not in seen:seen.add(k);out.append((s,J))
 return rs,out

if __name__=='__main__':
 import time;tic=time.monotonic();U=ordered();h=(MATES[0],MATES[0],MATES[0],MATES[1]);H=typegraph(*h)
 assert len(set(ordkey(H,w) for w in permutations(range(3))))==1
 H3=(h,IDENTITY[:3],1);assert U[0]==H3
 charts=[x for x in U if x[1]==(0,1,2)];assert len(charts)==len(make())==11
 for ind,u in enumerate(charts):
  q,w,d=u;g=typegraph(*q);es=[(a,b) for a,b in combinations(range(12),2) if b in g[a] and a//4!=b//4 and not(g[a]&g[b])]
  if es: gs=[g,H,H];ps=[u,H3,H3];edge=es[0]
  else: gs=[H,H,g];ps=[H3,H3,u];edge=(0,4)
  C=startcase(gs,[w for p,w,d in ps],edge);groups,ors=seedreps(C,gs,ps);tables(C)
  print('chart',ind, 'permutations',q,'edge',edge,'anchor',bool(es),'seeds',len(C['seeds']),len(ors),flush=True)
  total=mx=0
  for seed in ors:
   a,nn,_=oneseed(C,seed);total+=nn;mx=max(mx,nn)
   assert a==0
  assert (total,mx)==list(zip([80707,50060,50669,90900,39769,38602,49607,83528,90831,111345,72516],[5354,4712,5553,7721,3691,3831,3706,5275,7433,4280,5380]))[ind]
  print('end',ind,total,mx,round(time.monotonic()-tic,1),flush=True)
