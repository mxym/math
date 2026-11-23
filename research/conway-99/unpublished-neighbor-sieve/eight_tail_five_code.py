#!/usr/bin/env python3
"""Exact four-check for eight contracted tails. Run beside connected_saturated_five_rank.py."""
import itertools as it
from collections import Counter
import numpy as np
from connected_saturated_five_rank import cay,cyc,key,parts,mate,perfect,lines
def ca(A):
 n=len(A[0]);unseen=set(range(n));cc=[]
 while unseen:
  x=min(unseen);W=[x];unseen.remove(x)
  for y in W:
   for a in A:
    if a[y] in unseen:unseen.remove(a[y]);W.append(a[y])
  p={y:j for j,y in enumerate(W)};B=[tuple(p[a[y]] for y in W) for a in A]
  cc.append(key(B))
 h=0;S=[]
 for c in sorted(cc,key=lambda c:(len(c),c)):S+=list(x+h for x in c);h+=len(c)//3
 return bytes(S)
def ksall(n):
 p=list(range(n));F=tuple(mate(e,n) for e in perfect(tuple(p))); out=set()
 for z in parts(n//2):
  co=[];ch=[]; l=0
  for k in z:
   for i in range(k):co.append((l+2*i,l+2*i+1));ch.append((l+2*i+1,l+((2*i+2)%(2*k))))
   l+=2*k
  a,b=mate(co,n),mate(ch,n)
  for c in F:
   A=(a,b,c); code=ca(A)
   if code not in out:
    codes=set(ca(tuple(A[j] for j in v)) for v in it.permutations(range(3)))
    out.update(codes);yield min(codes)
def min2(K):
 E,Z=cyc(K);n=len(K)//3;X=lines(len(Z))@Z%5
 # one omitted coordinate class per first two colors at tail zero
 f=0;g=n//2 # smallest edge index within its color is indeed 0-tail
 assert E[f][0]==E[g][0]==0
 # projective rows no need normal sorted; order solved by scaling field
 def anchored(f,g):
  V=X[(X[:,f]!=0)&(X[:,g]==0)&(np.count_nonzero(X,axis=1)==10)]
  Y=(V*np.array([0,1,3,2,4])[V[:,f],None])%5
  return Y[np.sum((Y==1)|(Y==4),axis=1)==5]
 P=anchored(f,g);Q=anchored(g,f); t=len(E)
 for h in P:
  q=Q[Q@h%5==0]
  for j in range(1,5):
   v=(h+j*q)%5;q=q[(np.count_nonzero(v,axis=1)==10)&(np.sum((v==1)|(v==4),axis=1)==5)]
  for y in q:yield np.array([h,y])
def wlab(K,extra=False):
 E,Z=cyc(K);n=len(K)//3;N=3*n;tail=np.array([t for e in E for t in e]);col=np.arange(N)//n
 D=np.array([[int(x!=y and (tail[x]==tail[y] or x//2==y//2)) for y in range(N)] for x in range(N)])
 M=2-D-D@D-(col[:,None]==col[None,:]).astype(int);np.fill_diagonal(M,0)
 assert np.min(M)>=0
 tag=np.array([a for a in it.combinations(range(N),n//2) if len(set(tail[list(a)]))==len(a) and all(list(col[list(a)]).count(k)<=2 for k in range(3))],int)
 i,j=np.triu_indices(n//2,1);pa=tag[:,i]*N+tag[:,j];Q=np.triu(M).ravel()
 keep=np.all(Q[pa]>0,axis=1);return Q,pa[keep],tag[keep]
def span2(M,b):
 R={}
 for u in M:
  while u and u.bit_length() in R:u^=R[u.bit_length()]
  if u:R[u.bit_length()]=u
 while b and b.bit_length() in R:b^=R[b.bit_length()]
 return b==0
def f2(Y,V):
 Q,pa,tag=V;N=2*Y.shape[1]
 lab=(np.repeat(Y,2,axis=1)*np.tile([1,-1],N//2)).T
 good=np.all(np.sum(lab[tag],axis=1)%5==0,axis=1)
 rhs=sum(1<<int(i) for i in np.flatnonzero(Q%2))
 return span2([sum(1<<int(i) for i in a) for a in pa[good]],rhs)

def main():
 A=Counter();B=Counter()
 for K in ksall(8):
  _,Z=cyc(K); c=len(Z)-4;A[c]+=1
  V=wlab(K)
  for Y in min2(K):
   assert not f2(Y,V),(K.hex(),Y.tolist())
   B[c]+=1
 assert A=={1:19,2:9,3:2,4:1} and B=={1:40,2:480,3:1152,4:31104}
 print('Contraction catalog by component count:',sorted(A.items()))
 print('F2-inconsistent four-site pair-quota tables:', sorted(B.items()))
if __name__=='__main__':main()
