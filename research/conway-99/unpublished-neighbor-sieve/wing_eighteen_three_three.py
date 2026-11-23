"""Exact rejection of the dimension-3 + dimension-3 pair. Python 3 + NumPy.
Default: verify the full finite proof (~120 s on one core). No optimizer, network, or input files.
"""
from itertools import permutations,product,combinations
from collections import Counter,defaultdict
import numpy as np
I=tuple(range(6));P=(1,0,3,2,5,4)
def blocks(q,r,f):
 N=[set() for i in range(18)]
 for i in I:
  for a,b in [(i,P[i]),(i+6,6+q[i]),(12+i,12+r[i]),(i,6+i),(6+i,12+i),(12+i,f[i])]:
   N[a].add(b);N[b].add(a)
 return N
def kval(G):
 A=[[3*(i==j)-int(j in G[i]) for j in range(18)] for i in range(18)]+[[1]*18]
 return kernel(A)
def kernel(a):
    A=[[v%7 for v in r] for r in a];m=len(A);n=len(A[0]);piv=[]
    for j in range(n):
        t=len(piv);r=next((i for i in range(t,m) if A[i][j]),None)
        if r is None:continue
        A[t],A[r]=A[r],A[t];inv=pow(A[t][j],-1,7)
        A[t]=[v*inv%7 for v in A[t]]
        for i in range(m):
            if i!=t:
                q=A[i][j];A[i]=[(v-q*u)%7 for v,u in zip(A[i],A[t])]
        piv.append(j)
    B=[]
    for f in sorted(set(range(n))-set(piv)):
        x=[0]*n;x[f]=1
        for i,j in enumerate(piv):x[j]=-A[i][f]%7
        B.append(tuple(x))
    return B




def automorphisms(G):
 # A permutation of the three wings and of six sites of the first wing determines any isomorphism:
 # images in each of the other wings are forced by the cross-wing perfect matchings.
 for w in permutations(range(3)):
  for p in permutations(range(6)):
   z=[None]*18
   for i in range(6):z[i]=6*w[0]+p[i]
   for u in (1,2):
    for i in range(6):
     j,=(x for x in G[i] if x//6==u)
     v,=(x for x in G[z[i]] if x//6==w[u])
     z[j]=v
   if all({z[j] for j in G[i]}==G[z[i]] for i in range(18)):yield w,z
rr=(2,4,0,5,1,3),(1,0,5,4,3,2)
G=blocks(*rr,(3,5,4,1,2,0));K=kval(G);assert len(K)==3
autos=list(automorphisms(G))
assert len(autos)==12 and len({w for w,z in autos})==6
assert any(w==(0,1,2) and all((h[i]+h[z[i]])%7==0 for i in range(18) for h in K) for w,z in autos)
A=(G,K)
def setup(S):
 G,K=S;m={(i,j):2-int(j in G[i])-len(G[i]&G[j])-int(i//6==j//6) for i,j in combinations(range(18),2)};pp=[v for v,mv in m.items() if mv>0]
 E=[v for v in combinations(range(18),3) if all(m[k]>0 for k in combinations(v,2)) and len({i//6 for i in v})>=2 and all(len(G[i].intersection(v))+int(i in v)<=2 for i in range(18))]
 K=np.array(K);sig=np.array([K[:,list(e)].sum(axis=1)%7 for e in E]);wing=np.array([sum(4**i*sum(v//6==i for v in e) for i in range(3)) for e in E]);rows=[[pp.index(q) for q in combinations(e,2)] for e in E]
 return E,pp,m,sig,wing,rows
def testeq(d,L,R,M,par=True):
 E,p,m,Z,w,rr=L;F,q,n,Y,u,ss=R;hv=(Z@(7**np.arange(d)))%7**d if Z.shape[1]==d else ((Z[:,:d])@(7**np.arange(d)))%7**d;g=((Y@M.T%7)@(7**np.arange(d)))%7**d
 D=defaultdict(list);O=len(p)+len(q);rhs=[m[x] for x in p]+[n[x] for x in q]+[2-int(i//6==j//6) for i in range(18) for j in range(18)]
 for j,(t,wp) in enumerate(zip(g,u)):D[int(t),42-int(wp)].append(j)
 base={};cap=Counter();nv=0
 for i,(h,lw) in enumerate(zip(hv,w)):
  for j in D[int(h),int(lw)]:
   nv+=1;rs=rr[i]+[len(p)+z for z in ss[j]]+[O+18*a+b for a in E[i] for b in F[j]];cap.update(rs)
   if par:
    t=sum(1<<z for z in rs)
    while t and t.bit_length() in base:t^=base[t.bit_length()]
    if t:base[t.bit_length()]=t
 if any(cap[i]<z for i,z in enumerate(rhs)):return 'cell'
 if not par:return 'pass'
 b=sum((x%2)<<i for i,x in enumerate(rhs))
 while b and b.bit_length() in base:b^=base[b.bit_length()]
 return 'parity' if b else 'pass'

from time import monotonic
def scan33(maxrow=171):
 E,P,m,sig,wp,rows=setup(A)
 S3=list(product(range(7),repeat=3)); h3idx={v:i for i,v in enumerate(S3)}
 sig=[tuple(map(int,s)) for s in sig]
 vcode=[h3idx[v] for v in sig];wp=list(map(int,wp))
 D=[[sum(x*y for x,y in zip(a,b))%7 for b in S3] for a in S3]
 mask=[[sum(1<<j for j,z in enumerate(row) if z==k) for k in range(7)] for row in D]
 All=(1<<343)-1
 right=sorted({(42-p,v) for p,v in zip(wp,vcode)})
 keys3=[(p,s[0],s[1],s[2]) for p,s in zip(wp,sig)]
 bucketE=[[] for p in P]
 for z,row in enumerate(rows):
  for j in row:bucketE[j].append(z)
 pidx=sorted(range(len(P)),key=lambda z:(len(bucketE[z])-m[P[z]],-m[P[z]]))
 
 left=np.zeros((64,343,18),dtype=np.int8); vv=np.array(vcode,int);WP=np.array(wp,int);Dmat=np.array(D,np.int16)
 for e,v,w in zip(E,vcode,wp):
  for i in e:left[w,v,i]+=1
 ids=[np.array([z for z,e in enumerate(E) if j in e]) for j in range(18)]
 lmask=np.any(left,axis=2);pdim=max(map(len,bucketE));pairs=np.array([lst+[len(E)]*(pdim-len(lst)) for lst in bucketE],dtype=np.int16);thr=np.array([m[e] for e in P],int)
 minq=[np.array([2-int(i//6==j//6) for i in range(18)]) for j in range(18)]
 t0=monotonic();cnt=Counter();cases=[]
 for ai,a in enumerate(S3):
  if not any(a) or next(x for x in a if x)>3:continue
  # source buckets indexed by left signature (two first exact components) and complementary wing
  for bi,b in enumerate(S3):
   norm=((a[1]*b[2]-a[2]*b[1])%7,(a[2]*b[0]-a[0]*b[2])%7,(a[0]*b[1]-a[1]*b[0])%7)
   if not any(norm):continue
   cnt['partials']+=1;available=All^mask[h3idx[norm]][0]
   buckets=defaultdict(list);D0=D[ai];D1=D[bi]
   for w,v in right:buckets[w,D0[v],D1[v]].append(v)
   cm={}
   for j in pidx:
    u=v0=0
    for eid in bucketE[j]:
     key=keys3[eid]
     if key not in cm:
      w,f,g,h=key;v=0
      for q in buckets.get((w,f,g),()):v|=mask[q][h]
      cm[key]=v
     v=cm[key];v0|=u&v;u|=v
    available&=u if m[P[j]]==1 else v0
    if not available:break
   if available:
    cnt['after_left']+=available.bit_count()
    
    cand=[]
    while available:
     v=available&-available;available-=v;cand.append(v.bit_length()-1)
    qv0=np.array(cand)
    sig2=49*Dmat[ai,vv]+7*Dmat[bi,vv]
    w2=sig2[None,:]+Dmat[np.ix_(qv0,vv)]
    can=lmask[(42-WP)[None,:],w2]
    can=np.pad(can,((0,0),(0,1)))
    qv0=qv0[np.all(can[:,pairs].sum(axis=2)>=thr[None,:],axis=1)]
    cnt['after_reverse']+=len(qv0)
    for j,rid in enumerate(ids):
     if not len(qv0):break
     ws=42-WP[rid];w2=sig2[rid][None,:]+Dmat[np.ix_(qv0,vv[rid])]
     within=left[ws[None,:],w2,:].sum(1)
     qv0=qv0[np.all(within>=minq[j][None,:],axis=1)]
     if not len(qv0):break
    cnt['after_cross']+=len(qv0)
    for cn in qv0:
     M=np.array([a,b,S3[cn]])
     stat=testeq(3,setupA,setupA,M);cnt[stat]+=1
     if stat=='pass':cases.append((ai,bi,cn))
  cnt['a']+=1
  if cnt['a']%50==0:print('done first rows',cnt['a'],flush=True)
  if cnt['a']>=maxrow:break
 assert cnt==Counter(a=171,partials=57456,after_left=896500,after_reverse=103831,after_cross=27568,parity=27568) and not cases
 print('all 16892064 maps up to sign rejected:',dict(cnt),round(monotonic()-t0,2),'seconds')
setupA=setup(A);assert len(setupA[0])==612
scan33()
