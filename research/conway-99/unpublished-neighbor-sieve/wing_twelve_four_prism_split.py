"""Rank36 four-prism/12-component splitter theorem, exact 12-far-site proof.
Standalone NumPy integers; the twelve-component library at top reproduces twelve_sites.py.
No solver or global case search. All chart numbers are necessary diagrams, not graphs.
"""
from collections import Counter
from itertools import combinations, permutations, product


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


def chart(p, q, r, return_map):
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
    graph = chart(*parameters)
    keys = []
    for a,b,c in ((0,1,2),) if ordered_wings else permutations(range(3)):
        for order in permutations(range(4*a,4*a+4)):
            second = [next(j for j in graph[i] if j//4 == b) for i in order]
            third = [next(j for j in graph[i] if j//4 == c) for i in second]
            labels = list(order) + second + third
            keys.append(tuple(int(labels[j] in graph[labels[i]]) for i,j in combinations(range(12),2)))
    return min(keys)


def verify_dual(parameters, weights):
    graph = chart(*parameters)
    count = {pair:m for pair,m in multiplicities(graph).items() if m}
    assert min(count.values()) > 0 and sum(count.values()) == 60
    demand = {e: [2 - int(i in e) - len(graph[i].intersection(e)) for i in range(12)]
              for e in count}
    assert all(min(row) >= 0 and sum(row) == 16 for row in demand.values())
    zero = (0,)*12
    left = sum(count[e]*sum(a*b for a,b in zip(weights[e],demand[e])) for e in weights)
    right = 0
    for e,f in combinations(count,2):
        if any(demand[e][i] == 0 for i in f) or any(demand[f][i] == 0 for i in e):
            continue
        value = sum(weights.get(e,zero)[i] for i in f) + sum(weights.get(f,zero)[i] for i in e)
        right += min(count[e],count[f])*max(value,0)
    assert left > right
    return left, right



def w12root():
 named={};ex=[code(u) for u in CERTIFICATES]
 for q,r,f in product(MATES,MATES,permutations(range(4))):
  u=MATES[0],q,r,f;g=chart(*u)
  if not connected(g) or min(multiplicities(g).values())<0:continue
  nm=code(u)
  if nm in ex:continue
  keys=[]
  for a,b,c in ((0,1,2),(0,2,1)):
   for order in permutations(range(4)):
    ss=[next(j for j in g[i] if j//4==b) for i in order]
    tt=[next(j for j in g[i] if j//4==c) for i in ss]
    perm=list(order)+ss+tt;keys.append(tuple(int(perm[j] in g[perm[i]])for i,j in combinations(range(12),2)))
  named.setdefault(min(keys),u)
 return list(named.values())
from collections import defaultdict
def pairs12(g):
 E=[e for e,v in multiplicities(g).items() if v>0 and min(e)>=4]
 return [es for es in combinations(E,4) if len(set(sum(es,())))==8]

import numpy as np
from collections import defaultdict
def batrank(a):
 a=np.array(a,dtype=np.int16)%7
 n,m,k=a.shape;rr=np.zeros(n,dtype=int);R0=np.arange(n)
 for col in range(k):
  ci=(np.arange(m)[None,:]>=rr[:,None])&(a[:,:,col]!=0)
  good=ci.any(1);w=R0[good]
  if not len(w):continue
  pr=rr[w];i=ci[w].argmax(1)
  b=a[w,pr].copy();a[w,pr]=a[w,i];a[w,i]=b
  b=(a[w,pr]*np.array([0,1,4,5,2,3,6],dtype=np.int16)[a[w,pr,col]][:,None])%7
  a[w]=(a[w]-a[w,:,col,None]*b[:,None,:])%7;a[w,pr]=b;rr[w]+=1
 return rr
inv7=np.array([0,1,4,5,2,3,6],dtype=np.int16)
def invs(ss):
 n,d,_=ss.shape;a=np.tile(np.eye(d,dtype=np.int16),(n,1,1));b=ss.copy();row=np.arange(n);det=np.ones(n,np.int16)
 for j in range(d):
  non=b[:,j:,j]!=0;k=non.argmax(1)+j;det*=np.where(k==j,1,-1).astype(np.int16)
  for M in [a,b]:
   x=M[:,j].copy();M[:,j]=M[row,k];M[row,k]=x
  piv=b[:,j,j].copy();det=det*piv%7; iv=inv7[piv];b[:,j]=b[:,j]*iv[:,None]%7;a[:,j]=a[:,j]*iv[:,None]%7
  f=b[:,:,j].copy();f[:,j]=0;b=(b-f[:,:,None]*b[:,None,j])%7;a=(a-f[:,:,None]*a[:,None,j])%7
 return a,det


def aug(g):
 W=[{j+6*k for j in range(6) if (j==(i^1) or (i%2==j%2 and j!=i))} for k in range(4) for i in range(6)]+[{j+24 for j in n} for n in g]
 wing=np.array([i%6//2 for i in range(24)]+[i//4 for i in range(12)])
 return W,wing
def zz(g):
 W,wing=aug(g);D=np.array([[int(j in W[i]) for j in range(36)] for i in range(36)]);U=(3*np.eye(36,dtype=np.int16)-D+4)%7
 # principal nonsingular piece from symmetric elimination, permitting 2x2 pivots
 A=U.copy();I=[];left=set(range(36))
 while left:
  S=sorted(left);q=next((i for i in S if A[i,i]),None)
  if q is None:
   ef=next(((i,j) for i,j in combinations(S,2) if A[i,j]),None)
   if ef is None:break
   B=list(ef)
  else:B=[q]
  iv,_=invs(A[B,:][:,B][None]);A=(A-A[:,B]@iv[0]@A[B,:])%7;left-=set(B);I+=B
 inv,det=invs(U[I,:][:,I][None]);assert det[0];iv=inv[0]
 L=sorted(left);raw,rs=[],{};Bset={i+24 for i in range(4,12) if any(j<2 for j in g[i])}
 P=np.array(list(combinations(range(28,36),2)));m=multiplicities(g);P=np.array([e for e in P if m[tuple(e-24)]>0])
 for e in P:
  for pos in combinations(range(3),2):
   for p in product(*[[0,1] if i in pos else [2,3,4,5] for i in range(4)]):
    v=tuple(p[i]+6*i for i in range(4))+tuple(e)
    if np.min(np.bincount(wing[list(v)],minlength=3))!=2:continue
    rs[tuple(p)+tuple(e)]=len(raw);raw.append(v)
 raw=np.array(raw,dtype=np.int16);inc=np.zeros((len(raw),36),dtype=np.int16);inc[np.arange(len(raw))[:,None],raw]=1
 Bmarks=4-inc;proj=(Bmarks[:,I]@iv)%7
 lin=(Bmarks[:,L]-proj@U[I,:][:,L])%7
 r0=batrank(lin[None])[0]
 J=[]
 for j in range(len(L)):
  if batrank(lin[:,J+[j]][None])[0]>len(J):J.append(j)
 if len(J):lin=lin[:,J]
 else:lin=np.zeros((len(raw),0),dtype=np.int16)
 assert len(I)+lin.shape[1]==32
 pg=(4-proj@Bmarks[:,I].T)%7 # raw mark 3I - A + 1/9; add 3 on diagonals and subtract A
 eq=inc@inc.T
 return I,lin,pg,inc,raw,rs,Bset,D,wing
def diags(g,rs,Bs,a,b,split):
 es0=[]
 for es in pairs12(g):
  L=np.array(es)+24
  if split and any(sum(i in Bs for i in e)!=1 for e in L):continue
  es0+=list(permutations(tuple(map(tuple,L))))
 pp=list(permutations(range(2,6)));F=[i for i in range(4) if i not in (a,b)];out=[]
 E=[[None]*4 for i in range(4)]
 for i in range(4):E[i][a]=i//2;E[i][b]=i%2
 for p,q in product(pp,repeat=2):
  for i in range(4):E[i][F[0]]=p[i];E[i][F[1]]=q[i]
  z=[tuple(r) for r in E]
  for L in es0:
   key=[z[i]+L[i] for i in range(4)];ids=[rs.get(k,-1) for k in key]
   if min(ids)>=0:out.append(ids)
 return np.array(out,dtype=np.int16)
def squaregood(ww,pg,lin):
 d=lin.shape[1];K=pg[ww[:,:,None],ww[:,None,:]].copy()
 E=np.array([[int((i^j) in (1,2)) for j in range(4)] for i in range(4)],dtype=np.int16)
 K=(K-E+3*np.eye(4,dtype=np.int16))%7
 gram=np.zeros((len(ww),d+4,d+4),dtype=np.int16);gram[:,d:,d:]=K
 gram[:,:d,d:]=lin[ww].transpose(0,2,1);gram[:,d:,:d]=lin[ww]
 return gram,batrank(gram)
g12=w12root()

AD4=np.array([[int((i^j) in (1,2)) for j in range(4)] for i in range(4)],np.int16)
def solo(E,inc,D):
 z=inc[E];return ((z@(D+np.eye(36,dtype=np.int16))+AD4@z)<=2).all((1,2))
def auto12(g):
 left=range(4)
 for order in permutations(left):
  for b,c in ((1,2),(2,1)):
   perm=list(order)
   for wing in (1,2):
    for i in range(4*wing,4*wing+4):
     par=next(j for j in g[i] if j<4)
     perm.append(next(j for j in g[order[par]] if j//4==(b if wing==1 else c)))
   if all({perm[j] for j in g[i]}==g[perm[i]] for i in range(12)):
    yield np.array(perm),int(b==2)
def canonX(g,rs,raw,X):
 # flip a,y (with corresponding row permutations) and free prism bits z,d; simultaneous wing swap only together with a verified 12-template map.
 idcode=np.array([np.arange(len(X))]).flatten(); lookup={tuple(row):k for k,row in enumerate(X)};good=np.ones(len(X),bool)
 # build finite maps on words; only need those taking XX inputs to same two-parent subset
 for perm,sw in auto12(g):
  for s in range(16):
   letter=(raw[:,:4]%6)^((s>>np.arange(4))&1)[None,:]
   if sw:letter=np.where(letter>=2,2+((letter-2)^2),letter)
   sets=np.sort(24+perm[raw[:,4:6]-24],axis=1)
   R=np.column_stack((letter,sets));ids=np.array([rs[tuple(p)] for p in R])
   pr=[j^(((s&1)<<1)|((s&2)>>1)) for j in range(4)]
   good&=np.array([tuple(row)<=tuple(r) for row,r in zip(X,ids[X][:,pr])])
 return np.where(good)[0]

def setup12(j):
 g=chart(*g12[j]);I,lin,pg,inc,raw,rs,Bs,D,wing=zz(g);d=lin.shape[1]
 windows=[]
 for a,b,split in [(0,1,1),(0,2,1),(1,2,0)]:
  zz0=diags(g,rs,Bs,a,b,split);zz0=zz0[solo(zz0,inc,D)]
  G,R=squaregood(zz0,pg,lin)
  windows.append((zz0,G[:,list(range(d+3))][:,:,list(range(d+3))],R))
 X=windows[0][0]
 reps=canonX(g,rs,raw,X)
 m=2-D-D@D-(wing[:,None]==wing[None,:])
 pairbad=(inc@inc.T)>2
 for u,v in combinations(range(36),2):
  if m[u,v]<2:
   q=np.where(inc[:,u]*inc[:,v])[0]
   if len(q):pairbad[np.ix_(q,q)]=1
 return I,lin,pg,inc,raw,rs,Bs,D,wing,reps,pairbad,windows,m
def XYP(s,windows,pg,bad,d):
 X,Xg,_=windows[0];Y,Yg,_=windows[1];mask=~bad[X[s]][:,Y].any((0,2));jj=np.where(mask)[0]
 n=len(jj);G=np.zeros((n,d+6,d+6),np.int16)
 G[:,:d+3,:d+3]=Xg[s];L=list(range(d))+list(range(d+3,d+6))
 G[:,np.array(L)[:,None],np.array(L)[None,:]]=Yg[jj]
 p=pg[X[s,:3]][:,Y[jj,:3]].transpose(1,0,2)
 G[:,d:d+3,d+3:]=p;G[:,d+3:,d:d+3]=p.transpose(0,2,1)
 return jj,G,batrank(G)

def three(s,pack):
 I,lin,pg,inc,raw,rs,bs,D,wing,reps,bad,win,m=pack;d=lin.shape[1];top=4+d
 X,Xg,_=win[0];Y,Yg,_=win[1];Z,Zg,_=win[2];uZ,inv=np.unique(Z,return_inverse=True);zi=inv.reshape(Z.shape)
 cls=[np.unique(zi[:,k]) for k in range(4)]
 sel,G,rk=XYP(s,win,pg,bad,d)
 ct=Counter();store=[]
 for h in range(min(rk,default=0),top+1):
  carry=(rk==h)
  if not carry.any():continue
  ct['pair',h]=sum(carry)
  for II in combinations(range(d+6),h):
   if not carry.any():break
   take=np.where(carry)[0];J=list(II);bi,det=invs(G[take][:,J,:][:,:,J]);kk=det!=0
   if not kk.any():continue
   rr=take[kk];bi=bi[kk];carry[rr]=0
   for start in range(0,len(rr),32):
    ix=rr[start:start+32];B=bi[start:start+32];gy=G[ix];rows=Y[sel[ix]]
    ok=(~bad[X[s]][:,uZ].any(0))[None,:]&(~bad[rows][:,:,uZ].any(1))
    w=np.concatenate((np.tile(lin[uZ].T[None],(len(ix),1,1)),np.tile(pg[X[s,:3]][:,uZ][None],(len(ix),1,1)),pg[rows[:,:3]][:,:,uZ]),1)
    if h+1>=top:
     proj=B@w[:,J]%7;ok&=(((gy[:,:,J]@proj)%7)==w).all(1)
     if h==top:ok&=((proj*w[:,J]).sum(1)%7==(3+pg[uZ,uZ])%7)
    okk=ok.copy()
    # Any x,y hitting the same two wing sites have exhausted their quota before Z.
    for i0 in range(4):
     col=inc[rows]*inc[X[s,i0]][None,None,:]
     for i1 in range(4):
      dual=col[:,i1];w2=np.where(dual.sum(1)==2)[0]
      if not len(w2):continue
      ka,kb=np.nonzero(dual[w2])[1].reshape(-1,2).T
      okk[w2]&=~((inc[uZ][:,ka]*inc[uZ][:,kb]).T.astype(bool))
    go=np.where(np.stack([okk[:,L].any(1) for L in cls],1).all(1))[0]
    for i in go:
     zz=np.where(okk[i,zi].all(1))[0]
     if not len(zz):continue
     ct['checked3',h]+=len(zz)
     cz=w[i,:,zi[zz,:3]].transpose(0,2,1)
     ga=np.zeros((len(zz),d+9,d+9),np.int16);ga[:,:d+6,:d+6]=gy[i];ga[:,:d+6,d+6:]=cz;ga[:,d+6:,:d+6]=cz.transpose(0,2,1)
     ga[:,d+6:,d+6:]=Zg[zz,d:,d:];rz=batrank(ga)
     for k in np.where(rz<=top)[0]:
      ct['good3',int(rz[k])]+=1;store.append((int(s),int(sel[ix[i]]),int(zz[k]),h,int(rz[k])))
  assert not carry.any()
 return ct,store

if __name__=='__main__':
 import time
 assert len(g12)==21
 for old,w in CERTIFICATES.items():verify_dual(old,w)
 expected=[180,144,196,204,320,204,176,280,280,156,156,176,168,120,168,264,84,152,84,300,312]
 results=[];t0=time.time()
 for j,u in enumerate(g12):
  a=setup12(j);tic=time.time();tot=Counter();gr=[]
  for s in a[9]:
   ct,sd=three(s,a);tot.update(ct);gr+=sd
  assert len(a[9])==expected[j] and not gr
  z=(j,len(a[9]),len(gr),{str(k):int(v) for k,v in tot.items()})
  results.append(z);print('DONE',j,len(a[9]),len(gr),'good',gr[:4],round(time.time()-tic,1),round(time.time()-t0,1),z[-1],flush=True)
 print('all-results',results,flush=True)
