"""Independent finite checks for the general fixed-q results. Stdlib, no asserts."""
from itertools import permutations,combinations,product
from math import comb
from collections import Counter
from functools import lru_cache
from fractions import Fraction

def inv(p):
 return sum(x>y for i,x in enumerate(p) for y in p[i+1:])
def pat(a):
 return tuple(1+sum(y<x for y in a) for x in a)
def contains(p,b):
 ids=list(range(len(b)))
 def extend(t,z,vs):
  if t==len(b):return True
  for i in range(z,len(p)-len(b)+t+1):
   if all((p[i]<v)==(b[t]<b[j]) for j,v in enumerate(vs)) and extend(t+1,i+1,vs+(p[i],)):return True
  return False
 return extend(0,0,())
@lru_cache(None)
def avoid(p,B):
 return not any(contains(p,b) for b in B)
def components(p):
 o=[]; s=0; M=0
 for i,x in enumerate(p,1):
  M=max(M,x)
  if M==i:o.append(tuple(y-s for y in p[s:i]));s=i
 return tuple(o)
def core(p):return tuple(c for c in components(p) if len(c)>1)
def grow(c,g):
 p=[]
 for i,u in enumerate(c):
  for _ in range(g[i]):p.append(len(p)+1)
  j=len(p);p.extend(j+x for x in u)
 for _ in range(g[-1]):p.append(len(p)+1)
 return tuple(p)
def check_cuts(p,cap):
 n=len(p);I=sorted((max(i,j,p[i-1],p[j-1]),min(i,j,p[i-1],p[j-1])) for i in range(1,n+1) for j in range(i+1,n+1) if p[i-1]>p[j-1]);S=[]
 for b,a in I:
  if not S or a>S[-1]:S.append(b)
 if len(S)>cap:raise ValueError('packing')
 X=[];Y=[];rem=[]
 for i,x in enumerate(p,1):
  if i in S or x in S:continue
  if any(min(i,x)<c<max(i,x) for c in S):X.append(i);Y.append(x)
  else:rem.append(x)
 if rem!=sorted(rem):raise ValueError('diagonal cells')
 if S and max(sum(min(abs(t-s) for s in S) for t in Z) for Z in (X,Y))>2*inv(p):raise ValueError('distance')
def main():
 cases=(((1,3,2,4),),((2,1,4,3),),((2,1,4,3,6,5),),((1,3,2,4),(2,3,1)))
 K=4; N=7
 cores={():0}; allp=[list(permutations(range(1,n+1))) for n in range(N+1)]
 for ps in allp:
  for p in ps:
   k=inv(p)
   if k<=K: cores[core(p)]=k
 tcb=0; tmp=0
 for B in cases:
  A=[Counter(inv(p) for p in ps if avoid(p,B)) for ps in allp]
  m=1
  while avoid(grow(((2,1),)*m,[0]*(m+1)),B):m+=1
  M=max(map(len,B))
  T=[Counter() for i in range(N+1)]; maxf=0
  for c,k in cores.items():
   if len(c)>=m or not avoid(grow(c,[0]*(len(c)+1)),B):continue
   h=sum(map(len,c))
   for g in product(range(M+1),repeat=len(c)+1):
    if not avoid(grow(c,g),B):continue
    f=g.count(M);maxf=max(maxf,f);a=h+sum(g);tmp+=1
    for n in range(a,N+1):T[n][k]+= (n==a) if not f else comb(n-a+f-1,f-1)
  for n in range(N+1):
   for k in range(K+1):
    if A[n][k]!=T[n][k]:raise ValueError(('tuples',B,n,k))
   for p in allp[n]:
    if avoid(p,B):check_cuts(p,m-1);tcb+=1
  r=min(inv(b) for b in B if all(len(z)<=2 for z in components(b)))
  if maxf!=r:raise ValueError(('degree',B,maxf,r))
 # literal low-inversion polynomial vs Linusson-Verkama stable range
 pnums=[1]+[0]*20
 for j in range(1,len(pnums)):
  for k in range(j,len(pnums)):pnums[k]+=pnums[k-j]
 p2=lambda k:sum(pnums[i]*pnums[k-i] for i in range(k+1))
 num=0
 for n,ps in enumerate(allp):
  A=Counter(inv(p) for p in ps if avoid(p,((1,3,2,4),)))
  for k in range(2*n-6):
   ex=p2(k)-4*p2(k-n+1)-6*sum(p2(i) for i in range(k-n+1))
   if A[k]!=ex:raise ValueError(('LV',n,k))
   num+=1
 print('4 finite bases; legal capped tuples:',tmp)
 print('exact truncated inversion profiles: 4 x 8 sizes x 5 inversion levels; PASS')
 print('transversal, increasing diagonal cells, and distance budget for',tcb,'avoiders: PASS')
 print('Linusson-Verkama coefficient checks in their exact range:',num,'PASS')
if __name__=='__main__':main()
