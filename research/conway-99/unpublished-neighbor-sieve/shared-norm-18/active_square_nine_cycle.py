"""Exact check for a 12-cycle edge. Requires Python 3 and NumPy >=2.0."""
import numpy as np, itertools as it
S=range(12);l=lambda i:i^1;r=lambda i:(i+(1 if i%2 else -1))%12
a=12;z=13;mate=lambda i:25-i if i>=12 else l(i)
tags=[(i,j)for i in range(14)for j in range(i+1,14)if mate(i)!=j]; ids={x:i for i,x in enumerate(tags)}
def mask(ed):return sum(1<<ids[tuple(sorted(pair))] for pair in set(tuple(sorted(x))for x in ed))
def bmask(X):return sum(1<<i for i in X)
def gen():
 i=0
 for xt in it.combinations(S,5):
  X=set(xt)
  if not {i,l(r(i)),r(l(i))}<=X or any(l(j)in X or r(j)in X for j in X):continue
  A=[z,*xt];B=[mate(x)for x in A];O=sorted(set(S)-set(A)-set(B)); U=sorted(X-{i})
  cut=[(k,j)for k in [z,i]for j in U]
  for b in it.permutations([v for v in B if v!=r(i)]):
   if any(t==mate(k)for k,t in zip(xt,b)):continue
   base=[(z,r(i)),*zip(xt,b)];tau=xt[b.index(a)]
   for jj in [1,2,3]:
    Y=U.copy();h=Y.pop(jj);j=Y.pop(0);add=[(h,j),tuple(Y)]; F=mask(cut+base+add)
    for f in it.combinations(U,2):
     E=[(O[0 if j in f else 1],mate(j))for j in U]
     yield bmask(X),tau,mask(base+add+E),F
base=list(gen());N=len(base)
def trans(y,i):return y if y>=12 else (i+(-y if i%2 else y))%12
def allrows(i):
 d=[ids[tuple(sorted((trans(a,i),trans(b,i))))]for a,b in tags]
 pre=[[1<<v for v in d[j:j+8]] for j in range(0,len(d),8)]
 lut=[[sum(t[j] for j in range(len(t)) if w>>j&1)for w in range(256)]for t in pre]
 def f(v):return sum(a[(v>>(8*j))&255]for j,a in enumerate(lut))
 R=[];mask64=(1<<64)-1
 for X,tau,w,e in base:
  v=f(w);q=f(e);xx=bmask(trans(j,i) for j in S if X>>j&1)
  R.append((xx,trans(tau,i),v&mask64,v>>64,q&mask64,q>>64))
 return np.array(R,dtype=np.uint64).T
RR=[allrows(i)for i in S]
def matrix(i,j):
 x=RR[i];y=RR[j];B=np.empty((N,(N+7)//8),np.uint8); pc=np.bitwise_count
 for k in range(0,N,48):
  xx=x[:,k:k+48,None];yy=y[:,None,:]
  c=lambda x,y:pc(x[0]&y[0])+pc(x[1]&y[1])
  ok=(xx[1]!=yy[1])&((xx[1]!=j)|((yy[0]>>np.uint64(i))&1).astype(bool))&((yy[1]!=i)|((xx[0]>>np.uint64(j))&1).astype(bool))
  adj=int(r(i)==j)
  ok&=c(xx[2:4],yy[2:4])==1-adj
  ok&=c(xx[2:4],yy[4:6])==3*(1-(((yy[0]>>np.uint64(i))&1)|adj))
  ok&=c(xx[4:6],yy[2:4])==3*(1-(((xx[0]>>np.uint64(j))&1)|adj))
  B[k:k+48,:]=np.packbits(ok,axis=1,bitorder='little')
 return B
assert len(tags)==84 and len(set(base))==N==5724
assert all(trans(l(i),j)==l(trans(i,j)) and trans(r(i),j)==r(trans(i,j)) for i in S for j in S)
C={j:matrix(0,j)for j in range(1,12)}
history=[N]
elig=np.ones(N,bool)
while True:
 u=np.packbits(elig,bitorder='little');n=sum((d&u).any(axis=1).astype(int) for d in C.values());v=(n>=8)&elig
 history.append(int(sum(v)))
 if np.array_equal(elig,v):break
 elig=v

assert history==[5724,2057,1561,1470,1418,1407,1407]
print('common fixed point:',history)
V=np.flatnonzero(elig); K=len(V);ALL=(1<<K)-1
B={}
for j,m in C.items():
 a=np.unpackbits(m[V],axis=1,bitorder='little')[:,V]
 B[j]=[int.from_bytes(x.tobytes(),'little')for x in np.packbits(a,axis=1,bitorder='little')]
def t_inv(j,i):return ((i-j)if j%2==0 else (j-i))%12
def inds(x):
 while x:
  b=x&-x; yield b.bit_length()-1;x-=b
def excluded(sub):
 D=dict.fromkeys(sub,ALL); queue=list(sub)
 for j in queue:
  for i in sub:
   if i==j:continue
   row=B[t_inv(i,j)];target=D[j]
   m=sum(1<<v for v in inds(D[i]) if row[v]&target)
   if not m:return True
   if m!=D[i]:D[i]=m;queue.append(i)
 return False

allsubs=list(it.combinations(S,9))
rep=lambda s:min(tuple(sorted(trans(i,j)for i in s))for j in S)
subsets=sorted(set(map(rep,allsubs)))
assert len(allsubs)==220 and len(subsets)==19
for sub in subsets:assert excluded(sub),sub
print('nine-index subsets:',len(allsubs),'quotient:',len(subsets),'all excluded by pairwise propagation')
