"""Exact arithmetic cover, literal small templates, and residual graph materializer.
Run from this directory. No published finite data or external graph library is used."""
from collections import defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
def need(test,msg):
 if not test:raise ValueError(msg)
def graph(n,mask):
 A=[set() for _ in range(n)]
 for h,(i,j) in enumerate(combinations(range(n),2)):
  if mask>>h&1:A[i].add(j);A[j].add(i)
 return A
def path(A,s,t):
 def go(a,S):
  if a==t:return 1
  SS=S|{a}
  return sum(go(b,SS) for b in A[a]-SS)
 return go(s,set())
def cycle(A):
 ans=0
 for s,ns in enumerate(A):
  B=[z-set(range(s+1)) for z in A]
  ans+=sum(path(B,i,j) for i,j in combinations([v for v in ns if v>s],2))
 return ans
def three(A):
 if len(A)<4:return False
 for r in (0,1,2):
  for bad in combinations(range(len(A)),r):
   v=next(i for i in range(len(A)) if i not in bad)
   S=set(bad)|{v};Q=[v]
   while Q:
    for w in A[Q.pop()]-S:Q.append(w);S.add(w)
   if len(S)!=len(A):return False
 return True
def augment(n,mask,B,X):
 A=graph(n,mask); h=n;A.append(set())
 def add(s,t):
  need(s!=t and s not in A[t],'non-simple');A[s].add(t);A[t].add(s)
 for s in B:add(s,h)
 for length in X:
  need(length>=1,'empty ordinary branch');s=0
  for _ in range(length):
   t=len(A);A.append(set());add(s,t);add(t,h);s=t
  add(s,1)
 return A
def coef(st):
 m,n,mask,bm=st;B=[j for j in range(n) if bm>>j&1];H0=graph(n,mask)
 H=[ns-{n} for ns in augment(n,mask,[],[1]*m)]; H[n]=set(); G=augment(n,mask,B,[1]*m)
 need(three(G),'base not 3-connected')
 p0=path(H0,0,1);p=m+p0
 a=sum(path(H,n+1,t) for t in B)
 b=cycle(H0)+m*p0+comb(m,2)+sum(path(H,s,t) for s,t in combinations(B,2))
 need(b+a*m+(p-1)*m*(m-1)==cycle(G),'base count')
 return p,a,b
def stats(m,M):
 R=[[0]*(M+1) for _ in range(m+1)];R[0][0]=1
 for i in range(1,m+1):
  for n in range(i,M+1):
   for x in range(1,n-i+2):R[i][n]|=R[i-1][n-x]<<comb(x,2)
 return R
def lengths(m,n,t,R):
 X=[]
 while m:
  for x in range(1,n-m+2):
   j=t-comb(x,2)
   if j>=0 and (R[m-1][n-x]>>j)&1:
    X.append(x);t=j;n-=x;m-=1;break
  else:raise ArithmeticError('invalid partition')
 need(n==t==0,'invalid partition endpoint')
 return X
def segments(bits):
 while bits:
  lo=(bits&-bits).bit_length()-1
  u=bits>>lo; width=(u^(u+1)).bit_length()-1
  yield lo,lo+width-1
  bits^=((1<<width)-1)<<lo
def V(N):
 L,r=(N-1)//8,(N-1)%8+1
 return 11*N*(N-1)-10*(8*comb(L,2)+comb(r,2))
def emit(fp,A,h,k):
 # Put the hub first to speed independent counting; changing labels preserves every count.
 perm=[h]+[i for i in range(len(A)) if i!=h];ids={u:i for i,u in enumerate(perm)}
 E=sorted((min(ids[i],ids[j]),max(ids[i],ids[j])) for i,ns in enumerate(A) for j in ns if j>i)
 print(k,len(A),len(E),*(i for e in E for i in e),file=fp)
def main():
 high={};low={}
 for line in Path('core-styles.txt').read_text().splitlines():
  group,*params=line.split();st=tuple(map(int,params));p,a,b=coef(st)
  if 'H' in group:
   need(st[0]==9 and st[1]==5 and p==12 and 0<=a<=161 and 0<=b<=266,'high bounds')
   high[a,b]=st
  if 'L' in group:low[st]=p,a,b
 with open('core-samples.txt','w') as f:
  for st in sorted(set(high.values())|set(low)):
   m,n,mask,bm=st;p,a,b=coef(st);B=[j for j in range(n) if bm>>j&1]
   for X in ([2]+[1]*(m-1),[1+(i%3) for i in range(m)],[3]+[2]*(m-1)):
    N=sum(X);k=b+a*N+(p-1)*N*(N-1)-(p-2)*sum(comb(x,2) for x in X)
    emit(f,augment(n,mask,B,X),n,k)
 allres=set(range(10))
 for x in range(10):need({(b+a*x+11*x*(x-1))%10 for a,b in high}==allres,'residue gap')
 print('High coefficient pairs:',len(high),'; low templates:',len(low),'; all 100 residue tests pass.')
 # For each N and style, represent a window of triangular sums T.
 # Convert windows [u,v] of T to intervals of quotients of k mod 10.
 lists=[[]for _ in range(10)]
 R9=stats(9,90)[9]
 for N in range(9,1501):
  if N<=90:Seg=list(segments(R9[N]))
  else:
   L=(N-1)//8;Seg=[]
   for z in {max(1,L-i) for i in [0,1,2,3,4,8]}:
    y=N-8*z;t=8*comb(z,2)+comb(y,2);Seg.append((t,t+(z-1)**2))
  for a,b in high:
   K=b+a*N+11*N*(N-1);r=K%10
   lists[r].extend((K//10-v,K//10-u) for u,v in Seg)
 top=V(1500);need(top==23342160,'anchor')
 holes=set()
 for r,L in enumerate(lists):
  last=(top-r)//10;next_=1 if r==0 else 0 # positive k only
  for lo,hi in sorted(L):
   if hi<next_:continue
   if next_>last:break
   if lo>next_:holes.update(10*j+r for j in range(next_,min(lo,last+1)))
   next_=max(next_,hi+1)
  if next_<=last:holes.update(10*j+r for j in range(next_,last+1))
 print('Uncovered positive integers through',top,'after high windows:',len(holes),'maximum:',max(holes))
 # Fill every remaining positive except the independently checked small exclusions.
 # Each claimed solution below is materialized and can be counted WITHOUT a formula.
 result={};cache={}
 for st,(p,a,b) in low.items():
  m,n,mask,bm=st;q=p-2;need(q>0,'low q')
  if m not in cache:cache[m]=stats(m,150)
  RR=cache[m]
  for N in range(m,151):
   K=b+a*N+(p-1)*N*(N-1);bits=RR[m][N]
   lo=K-q*(bits.bit_length()-1);hi=K-q*((bits&-bits).bit_length()-1)
   for k in tuple(holes):
    if lo<=k<=hi and (K-k)%q==0 and bits>>((K-k)//q)&1:
     result[k]=(st,lengths(m,N,(K-k)//q,RR));holes.remove(k)
 literal={}
 for line in Path('small-masks.txt').read_text().splitlines():
  k,n,mask=map(int,line.split())
  if k in holes:
   A=graph(n,mask);need(three(A) and cycle(A)==k,'small literal');literal[k]=A;holes.remove(k)
 missing=list(range(1,7))+list(range(8,13))+list(range(16,21))+[27,30,32,33,34]
 need(sorted(holes)==missing,'remaining gaps '+str(sorted(holes)))
 with open('residual-graphs.txt','w') as f:
  for k in sorted(result.keys()|literal.keys()):
   if k in literal:A=literal[k];h=0
   else:
    (m,n,mask,bm),X=result[k];A=augment(n,mask,[i for i in range(n) if bm>>i&1],X);h=n
   emit(f,A,h,k)
 print('Materialized residual witnesses:',len(result)+len(literal),'; remaining exceptions:',*missing)
if __name__=='__main__':main()
