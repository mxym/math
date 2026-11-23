"""Fixed-Fano two-star test. No solver or randomized choice. Requires numpy and sympy."""
import numpy as np, sympy as sp
from sympy.polys.matrices import DomainMatrix as DM
F=sp.GF(7);Q=lambda m:DM.from_Matrix(sp.Matrix(m)).convert_to(F)
AM=sp.zeros(14,14);p=0
for a in range(7):
 for b in range(7):
  AM[a,7+b]=AM[7+b,a]=((a+1)&(b+1)).bit_count()%2
sig=[j for j in range(7) if AM[p,7+j]];dou=[j for j in range(7) if not AM[p,7+j]]
tags=sig+sum(([v,v]for v in dou),[])
# actual matching between H(p) in the distinguished neighborhood;
# each double pair sends one of its copies to each other pair. All signs negative around the triangle.
pairs=[(4,7),(6,9),(8,5)]
from itertools import combinations,product
from collections import Counter
from math import comb
N=np.array([(int(i>=4),*(int(i==4+2*j)-int(i==5+2*j) for j in range(3))) for i in range(4,10)])
H=np.array([[0,0,0,0],[0,5,3,3],[0,3,5,3],[0,3,3,5]])
I=set((a-4,b-4) if a<b else (b-4,a-4) for a,b in pairs)|{(0,1),(2,3),(4,5)}
edges=[k for k in combinations(range(6),2) if k not in I]
Eall=np.array([np.outer(N[i],N[j])+np.outer(N[j],N[i])for i,j in edges])
keep=[];st=Counter()
for bits in product(range(2),repeat=9):
 D=np.array(bits)@np.array([np.eye(6,dtype=int)[i]+np.eye(6,dtype=int)[j]for i,j in edges])
 if max(D)>3:continue
 st['degs']+=1
 if sum(D)<6:continue # six degree3 dbls can accept twelve single incidence only; true lower 18-12=6
 st['capac']+=1
 M=(H-(np.array(bits)@Eall.reshape(9,-1)).reshape(4,4))%7
 r=Q(M.tolist()).rank()
 if r>4:continue
 st['rank']+=1
 if r==4:
  p=Q(M.tolist()).rref()[1];v=int(sp.Matrix(M.tolist())[p,p].det())%7
  if v not in [3,5,6]:continue
 st['type']+=1
 keep.append((bits,r,int(sum(D)//2),tuple(D)))
from itertools import permutations
# Binary Fano collineations of P-points taking p to p (indices bitvectors 1..7) and preserving dot with lines
def mob(P,i):
 return (P[0] if i&1 else 0)^(P[1] if i&2 else 0)^(P[2] if i&4 else 0)
group=[]
for Sx in permutations(range(2,8),2):
 M=(1,)+Sx;G0=[mob(M,i) for i in range(1,8)]
 if len(set(G0))<7:continue
 ng=[next((k for k in range(1,8) if all(((k&i).bit_count()-(a&j).bit_count())%2==0 for i,j in zip(G0,range(1,8)))),None) for a in range(1,8)]
 if None in ng:continue
 pm={i:sig.index(ng[t]-1) for i,t in enumerate(sig)}
 dp=[dou.index(ng[t]-1) for t in dou]
 for z in product([0,1],repeat=3):
  per=[pm[k] for k in range(4)]+[4+2*dp[k//2]+(k%2^z[k//2]) for k in range(6)]
  if {tuple(sorted((per[i],per[j])))for i,j in pairs}=={tuple(sorted((i,j)))for i,j in pairs}:break
 else:raise AssertionError
 group.append(per)
assert len({tuple(z) for z in group})==24 and len(keep)==281
def to_str(G):return tuple(sorted(tuple(sorted(e)) for e in G))
allpair=list(combinations(range(4),2));BY=Counter();reps=[]
for bits,r,ni,Dd in keep:
 D0set={(a+4,b+4) for take,(a,b) in zip(bits,edges) if take}
 smal=[q for q in group if to_str([(q[i],q[j])for i,j in D0set])==to_str(D0set)]
 if to_str(D0set)!=min(to_str([(q[i],q[j])for i,j in D0set])for q in group):continue
 for inn in combinations(allpair,ni-3):
  rem0=[3-sum(i in ab for ab in inn)for i in range(4)]
  proc=sorted(range(6),key=lambda j:abs(3-Dd[j]-2),reverse=True)
  def rec(j,rem,D):
   if j==len(proc):
    if any(rem):return
    A=to_str([*D0set,*inn,*D]);BY['label']+=1
    if A==min(to_str([(q[i],q[k])for i,k in A])for q in smal):reps.append(A);BY[ni]+=1
    return
   k=proc[j];c=3-Dd[k]
   for subset in combinations([i for i in range(4)if rem[i]],c):
    re=[r-(i in subset)for i,r in enumerate(rem)];rec(j+1,re,D+[(i,k+4) for i in subset])
  rec(0,rem0,[])
print('ordinary count',BY,len(reps),flush=True)

from functools import lru_cache
from itertools import combinations
from time import time
@lru_cache(None)
def baseW(q,n,h):
 Z=np.zeros((455,39),dtype=np.int16)
 for i,z in enumerate(combinations(range(15),3)):Z[i,np.array(z)+14]=1
 Z[:,q]=Z[:,7+n]=1
 for j in h:Z[:,29+j]=1
 return Z
def rrefg(A):
 A=np.array(A%7,dtype=np.int16);r=0;p=[]
 for j in range(A.shape[1]):
  rr=np.where(A[r:,j])[0]
  if len(rr)==0:continue
  k=r+rr[0];A[[r,k]]=A[[k,r]];A[r]=A[r]*pow(int(A[r,j]),-1,7)%7
  v=A[:,j].copy();v[r]=0;A=(A-v[:,None]*A[[r]])%7;p.append(j);r+=1
  if r==len(A):break
 return p,A
def makesource(D):
 A=np.zeros((39,39),dtype=np.int16);A[:14,:14]=np.array(AM.tolist(),dtype=np.int16)
 for j,n in enumerate(tags):A[0,29+j]=A[29+j,0]=A[7+n,29+j]=A[29+j,7+n]=1
 for j,k in pairs:A[29+j,29+k]=A[29+k,29+j]=1
 for z,(i,j) in enumerate(D,14):
  for k in [i,j]:A[z,29+k]=A[29+k,z]=1
 G=3*np.eye(39,dtype=np.int16)-A+4
 I,_=rrefg(G);rk=len(I);assert rk in [35,36]
 P,B=rrefg(np.column_stack([G[np.ix_(I,I)],np.eye(rk,dtype=np.int16)]));assert P==list(range(rk))
 V=B[:,rk:];J=[j for j in range(39)if j not in I]
 d=det7(G[np.ix_(I,I)]);assert d!=0
 delta=(3*pow(d,-1,7))%7 if rk==35 else 0
 assert rk==35 or d in [3,5,6]
 ext=V@G[np.ix_(I,J)]%7
 ca=A.T@A
 Ypairs=[(i,j)for i,j in combinations(range(10),2) if A[29+i,29+j]==0 and ca[29+i,29+j]==1]
 assert len(Ypairs)==24
 return A,I,V,J,ext,Ypairs,delta
def det7(M):
 A=np.asarray(M,dtype=np.int16).copy();d=1
 for i in range(len(A)):
  s=np.flatnonzero(A[i:,i]%7)
  if not s.size:return 0
  j=i+int(s[0]);
  if i!=j:A[[i,j]]=A[[j,i]];d=-d
  d=d*int(A[i,i])%7
  m=A[i+1:,i]*pow(int(A[i,i])%7,-1,7)%7;A[i+1:,i:]=(A[i+1:,i:]-m[:,None]*A[[i],i:])%7
 return d%7
@lru_cache(None)
def zspec(width):
 a=np.zeros((455,width),dtype=np.int16)
 for i,z in enumerate(combinations(range(15),3)):a[i,np.array(z)+14]=1
 return a
def prepstar(src,q):
 A,I,V,J,T,Ypairs,delta=src
 E=zspec(39);top=[];hs=[];modes=[]
 for n in range(7):
  for h in ([(i,)for i in range(10)] if AM[0,7+n] else Ypairs):
   a=np.zeros(39,dtype=np.int16);a[q]=a[7+n]=1
   for j in h:a[29+j]=1
   top.append(a);hs.append(h);modes.append(n)
 H=np.array(top,dtype=np.int16);Wb=4-H
 Wz=-E;N=len(I);k=Wb[:,I];z=Wz[:,I]
 d0=(k@T-Wb[:,J])%7;d1=(z@T-Wz[:,J])%7
 good=np.ones((len(H),455),dtype=bool)
 for j in range(len(J)):good&=((d0[:,None,j]+d1[None,:,j])%7==0)
 # base norms and cross
 zV=z@V%7; kV=k@V%7
 qq=(np.einsum('ij,ij->i',kV,k)[:,None]+np.einsum('ij,ij->i',zV,z)[None,:]+2*kV@z.T)%7
 choices=((0,) if delta==0 else range(7))
 rows=[];mo=[];vv=[];yy=[];xx=[]
 for h in choices:
  ii,jj=np.where(good&((qq+delta*h*h)%7==0))
  R=H[ii]+E[jj];ok=np.all(R@A+R<=2,axis=1)
  # Coexisting neighbors of a new row may not close an already saturated old pair.
  FULL=np.triu((A@A+A>=2),1).astype(np.int16)
  ok&= (np.einsum('ij,ij->i',R@FULL,R)==0)
  i,j=ii[ok],jj[ok]
  xx.append((k[i]+z[j])%7);yy.append((kV[i]+zV[j])%7);rows.append(R[ok]);mo.extend(modes[l]for l in i);vv.extend([h]*len(i))
 if any(mo.count(i)<2-int(AM[q,7+i]) for i in range(7)):return None
 C=np.vstack(rows);mo=np.array(mo);v=np.array(vv,dtype=np.int16)
 return mo,C,np.vstack(xx),np.vstack(yy),v,delta

# Standalone no-solver replay. Python3, numpy, sympy and node; optional [START END].
# Each index is a canonical first-star cubic diagram. Exit 0 means the specified
# interval was checked, not that its survivors can be completed.
import json,base64,subprocess,sys
JSCODE="\nconst population=u=>{u=(u>>>0)-((u>>>1)&0x55555555);u=(u&0x33333333)+((u>>>2)&0x33333333);return (((u+(u>>>4))&0xf0f0f0f)*0x1010101)>>>24};\nfunction solve(caseData,verbose=0) {\nconst {n,I,moB,Co,YB,hB,delta,init}=caseData, rank=I.length,\nmo=Buffer.from(moB,'base64'), C=Buffer.from(Co,'base64'),Y=Buffer.from(YB,'base64'),H=Buffer.from(hB,'base64');\nconst Q=[[0,0],[0,0]],sz=(n+31)>>5;\nconst contact=new Int32Array(n*7).fill(rank),ones=new Uint8Array(n),ab=new Uint32Array(n),ac=new Uint32Array(n),sums=new Int16Array(n);\nlet rowCols=[],columns=Array.from({length:32},()=>new Uint32Array(sz)),all=new Uint32Array(sz);\nfor(let i=0;i<n;i++){all[i>>5]|=(1<<(i&31));let ct=0,ids=[mo[i]], c0=0,c1=0;\nfor(let k=0;k<39;k++)if(C[39*i+k]){if(k<32)c0|=1<<k;else c1|=1<<(k-32);if(k>=14)ids.push(k-7);}\nfor(let k=0;k<rank;k++){if(C[39*i+I[k]]) contact[7*i+ct++]=k;sums[i]+=4*Y[i*rank+k];}\nones[i]=ct;ab[i]=c0;ac[i]=c1;rowCols.push(ids);for(let k of ids)columns[k][i>>5]|=1<<(i&31);\n}\n\nconst idx=new Int16Array(39).fill(-1);I.forEach((k,l)=>{idx[k]=l});const yy=Array.from({length:39},(_,k)=>{let a=new Uint8Array(n);if(idx[k]>=0)for(let j=0;j<n;j++)a[j]=Y[rank*j+idx[k]];return a});\nconst hcache=new Map(),zcache=new Map(),hidx=[],zidx=[],rm=new Uint32Array(n);\nfunction bucket(M,klist,header,h){\n const key=[h,...klist].join(',');\n if(M.has(key))return M.get(key);\n const b=new Uint8Array(n);\n if(header)for(let j=0;j<n;j++)b[j]=((sums[j]+h*delta*H[j])%7);\n for(let k of klist){let t=yy[k];for(let j=0;j<n;j++)b[j]+=7-t[j];}\n for(let j=0;j<n;j++)b[j]%=7;\n M.set(key,b);return b;\n}\nfor(let i=0;i<n;i++){let a=[],b=[];for(let k=0;k<39;k++)if(C[39*i+k]){if(k>=14&&k<29)b.push(k);else a.push(k);}\n hidx.push(bucket(hcache,a,true,H[i]));zidx.push(bucket(zcache,b,false,0));\n for(let k of rowCols[i])rm[i]|=1<<k;}\nlet nodes=0,edgesMade=0,probes=0;\nconst pool=Array.from({length:11},()=>new Int32Array(n)),ct=Array.from({length:11},()=>new Uint16Array(32));\nlet m1=0,m2=0;for(let k=0;k<32;k++){if(init[k]==1)m1|=1<<k;else m2|=1<<k;}\nfor(let i=0;i<n;i++)pool[0][i]=i;\nfunction rec(depth,len,m1,m2){\n nodes++;if(depth===10)return m1===0&&m2===0;\n let s1=0,s2=0;const P=pool[depth],F=pool[depth+1],cc=ct[depth];cc.fill(0);\n for(let z=0;z<len;z++){const l=rm[P[z]];s2|=s1&l;s1|=l;}\n if((m1&~s1)||(m2&~s2))return false;\n for(let z=0;z<len;z++){const l=rowCols[P[z]];for(let k of l)cc[k]++;}\n let best=-1,low=1e8,tar=m1|m2;\n while(tar){let b=tar&-tar;tar^=b;let k=31-Math.clz32(b),l=cc[k];let choices=m2&b?l*(l-1)/2:l;if(choices<low){low=choices;best=k;}}\n const B=1<<best;\n for(let j=0;j<len;j++){const i=P[j],mask=rm[i];if(!(B&mask))continue;\n const zeros=m1&mask,nm1=(m1&~mask)|(m2&mask),nm2=m2&~mask;\n const U=hidx[i],V=zidx[i],si=init[mo[i]]===1,ci=ab[i],cj=ac[i],tag=mo[i];\n let f=0,o1=0,o2=0;\n for(let k=0;k<len;k++){const g=P[k];if((k<=j&&B&rm[g])||(zeros&rm[g]))continue;\n const raw=U[g]+V[g],ip=raw>=7?raw-7:raw;if(ip!==3&&ip!==4)continue;\n if(ip===3&&(si||tag===mo[g]||init[mo[g]]===1))continue;\n if(population(ci&ab[g])+population(cj&ac[g])>ip-2)continue;\n F[f++]=g;const L=rm[g];o2|=o1&L;o1|=L;\n }\n if(f>=9-depth&&!(nm1&~o1)&&!(nm2&~o2)&&rec(depth+1,f,nm1,nm2))return true;\n }\n return false;\n}\n\nfunction start(){\n const ordered=Array.from({length:7},(_,i)=>i).filter(i=>init[i]===2);\n ordered.sort((a,b)=>{let na=0,nb=0;for(let i=0;i<n;i++){na+=mo[i]===a;nb+=mo[i]===b;}return na-nb;});\n const n1=ordered[0],n2=ordered[1];let first=0;\n for(let i=0;i<n;i++)if(mo[i]===n1){\n  const ci=ab[i],cj=ac[i],U=hidx[i],V=zidx[i],B=rm[i];\n  const sig=[],mate=[];const zeros=m1&B;\n  for(let j=0;j<n;j++){if(zeros&rm[j])continue;\n  const raw=U[j]+V[j],ip=raw>=7?raw-7:raw;\n  if(ip===4&&population(ci&ab[j])+population(cj&ac[j])<=2)sig.push(j);\n  if(mo[j]===n2&&ip===3&&population(ci&ab[j])+population(cj&ac[j])===1)mate.push(j);\n  }\n  const x1=(m1&~B)|(m2&B),x2=m2&~B;\n  for(let j of mate){first++;const D=rm[j];const y1=(x1&~D)|(x2&D),y2=x2&~D,zz=x1&D;\n  const T=hidx[j],W=zidx[j],c=ab[j],d=ac[j];let l=0,o1=0,o2=0;\n  for(let k of sig){if(rm[k]&zz)continue;const raw=T[k]+W[k];if(raw!==4&&raw!==11)continue;\n  if(population(c&ab[k])+population(d&ac[k])>2)continue;\n  const L=rm[k];o2|=o1&L;o1|=L;pool[2][l++]=k;\n  }\n  if(l>=8&&!(y1&~o1)&&!(y2&~o2)&&rec(2,l,y1,y2))return true;\n  }\n }\n return false;\n}\nlet ok=start();if(verbose)console.log(JSON.stringify({ok,n,nodes,edgesMade}));return {ok,n,nodes,edgesMade};}\n\nlet n=0,live=[],peak=0,nodes=0,start=Date.now(),counts={},rkct={},first=null,last=null;\nrequire('readline').createInterface({input:process.stdin}).on('line',line=>{const X=JSON.parse(line);if(first===null)first=X.ix;if(last!==null&&last+1!==X.ix)throw Error('non-contiguous');last=X.ix;const r=X.n===0?{ok:false,nodes:0}:solve(X);n++;nodes+=r.nodes;peak=Math.max(peak,r.nodes);if(r.ok)live.push(X.ix);counts[X.m]=(counts[X.m]||0)+1;rkct[X.rk]=(rkct[X.rk]||0)+1;if(n%500===0)console.log('checkpoint',last+1,'examined',n,'live',JSON.stringify(live),'max',peak,'seconds',((Date.now()-start)/1000).toFixed(1))}).on('close',()=>console.log('FINAL',JSON.stringify({first,last,n,live,peak,nodes,counts,rkct,seconds:Math.round((Date.now()-start)/100)/10})))"
enc=lambda a:base64.b64encode(np.asarray(a,dtype='u1').tobytes()).decode()
def jsdata(ix,D,q=1):
 sc=makesource(D);I=sc[1];d=int(sum(a>=4 and b>=4 for a,b in D));meta={'ix':ix,'m':d,'rk':len(I)}
 ans=prepstar(sc,q)
 if ans is None:return dict(meta,n=0)
 mo,C,X,Y,v,delta=ans
 return dict(meta,I=[int(i)for i in I],n=len(v),moB=enc(mo),Co=enc(C),YB=enc(Y),hB=enc(v),delta=int(delta),init=[2-int(AM[q,7+n])for n in range(7)]+[2]*15+[2-int(AM[q,7+n])for n in tags])
assert len(reps)==20907
lo,hi=(0,len(reps)) if len(sys.argv)==1 else map(int,sys.argv[1:])
assert 0<=lo<hi<=len(reps)
P=subprocess.Popen(['node','-e',JSCODE],stdin=subprocess.PIPE,text=True)
for ix in range(lo,hi):
 P.stdin.write(json.dumps(jsdata(ix,reps[ix]))+'\n')
P.stdin.close();rc=P.wait();assert rc==0
