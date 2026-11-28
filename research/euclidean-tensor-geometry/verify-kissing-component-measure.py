#!/usr/bin/env python3
"""Exact component-measure certificates. Python standard library only."""
import sys,math,json,zlib,base64
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
def add(a,b):return [(a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0)for i in range(max(len(a),len(b)))]
def scale(a,t): return [x*t for x in a]
def upper(f,lo,hi,n):
 # Rational Bernstein conversion and exact midpoint subdivision; the final
 # number is a global upper bound, regardless of the stopping tolerance.
 import heapq
 d=len(f)-1;h=hi-lo
 powc=[sum(f[k]*math.comb(k,j)*lo**(k-j)*h**j for k in range(j,d+1))for j in range(d+1)]
 B=[sum(powc[j]*Q(math.comb(i,j),math.comb(d,j))for j in range(i+1))for i in range(d+1)]
 den=math.lcm(*(x.denominator for x in B));a=[int(x*den) for x in B];lower=max(B[0],B[-1]);heap=[];s=0
 def put(v,D):
  nonlocal s
  s+=1;heapq.heappush(heap,(-Q(max(v),D),s,v,D))
 put(a,den)
 for _ in range(10000):
  ub,_,v,D=heapq.heappop(heap);ub=-ub
  if ub<=lower+Q(1,10**10):return ub
  xx=list(v);L=[];R=[]
  for i in range(d+1):
   L.append(xx[0]<<(d-i));R.append(xx[-1]<<(d-i));xx=[u+z for u,z in zip(xx,xx[1:])]
  D<<=d;R.reverse();lower=max(lower,Q(L[-1],D));put(L,D);put(R,D)
 return -heap[0][0]

class Template:
 def __init__(self,b64):
  d=json.loads(zlib.decompress(base64.b64decode(b64)));self.sz=d['sizes'];self.D=d['D'];self.N=len(self.sz);self.k=len(d['fac']);self.l=[Q(x,self.D)for x in d['lambda']]
  if min(self.l)<0 or self.D<=0:raise ValueError('bad multipliers')
  self.delta=[[Q(h,self.D**2)for h in a]for a in d['contrast']]
  if any(t<0 for a in self.delta for t in a):raise ValueError('bad PSD contrast')
  self.F=d['fac']
  if not (self.k==len(self.delta)>0 and len(self.l)==self.N>0):raise ValueError('inconsistent block dimensions')
  for mat,v in zip(self.F,self.delta):
   if len(mat)!=self.N or len(v)!=self.N or len(mat[0])<1 or any(len(row)!=len(mat[0]) for row in mat):raise ValueError('bad Gram factor dimensions')
   if any(type(z)is not int for row in mat for z in row):raise ValueError('nonintegral Gram factor')
  self.g=[[Q(1)],[Q(0),Q(1)]]
  for j in range(1,self.k):self.g.append(add([Q(0)]+scale(self.g[j],Q(2*j+5,j+5)),scale(self.g[j-1],Q(-j,j+5))))
 @lru_cache(None)
 def inner(self,i,j,delta):
  F=[Q(0)]
  for k,M in enumerate(self.F,1):
   x=Q(sum(a*b for a,b in zip(M[i],M[j])),self.D**2)
   if i==j:x+=delta*self.delta[k-1][i]
   F=add(F,scale(self.g[k],x))
  return F
 @lru_cache(None)
 def plain(self,i,j):
  F=self.inner(i,j,Q(0));return upper(F,Q(-1,2),Q(1,2),0)
 @lru_cache(None)
 def intr(self,i,t):
  F=self.inner(i,i,Q(t-1,t));L=self.l[i]
  A=add(F,[0,0,L/4,0,-L]);return upper(A,Q(-1),Q(1,2),0),sum(A)
 @lru_cache(None)
 def peer(self,i,t):
  if t==1:return Q(0)
  return upper(self.inner(i,i,Q(-1,t)),Q(-1,2),Q(1,2),0)
 @lru_cache(None)
 def diag(self,i,n,t,w):
  cap=Q(10**6,w);lo=Q(1,n);hi=min(Q(1),(64*cap+1)/49)if n in (5,7,9)else lo
  b,a=self.intr(i,t);return t*(self.l[i]*cap+max((1-lo)*b+lo*a,(1-hi)*b+hi*a)) + t*(t-1)*self.peer(i,t)
 def matrix(self,ss,cc,mp,W):
  m=len(ss);M=[[Q(0)]*m for _ in ss]
  for i in range(m):
   M[i][i]=self.diag(mp[i],ss[i],cc[i],W[ss[i]])
   for j in range(i):M[i][j]=M[j][i]=cc[i]*cc[j]*self.plain(mp[i],mp[j])
  return M
 def check(self,ss,cc,mp,t,W):
  if any(v<0 for v in t):raise ValueError('negative rescaling')
  M=self.matrix(ss,cc,mp,W);return sum(t[i]*t[j]*M[i][j]for i in range(len(t))for j in range(len(t)))

def residual(w,N,m):
 D=N-2*(m-1);L=N//5+1;INF=10**15
 # Lower bounds for each remaining sum/count after fixing a minimum odd part.
 ks=list(range(5,N+1,2));F=[];prev=None
 for i in range(len(ks),-1,-1):
  cc=[[INF]*L for _ in range(N+1)];cc[0][0]=0
  if i<len(ks):
   k=ks[i]
   for j in range(N+1):
    for b in range(j//5+1):
     cc[j][b]=min(prev[j][b],cc[j-k][b-1]+w[k] if j>=k and b else INF)
  F.append(cc);prev=cc
 F.reverse();out=set()
 def rec(j,b,i,budget,a):
  if F[i][j][b]>budget:return
  if not b:
   if j:raise ArithmeticError('nonzero unassigned sum')
   out.add(a);return
  for z in range(i,len(ks)):
   k=ks[z]
   if k*b>j:break
   rec(j-k,b-1,z,budget-w[k],a+(k,))
 for t in range((N-D)//2+1):
  for o in range(t+D,N-t+1,2):
   for s in range(min(o,t+132-N)+1):
    j=N-t-s;b=o-s
    if 5*b<=j:rec(j,b,0,84000000-s*w[1],(1,)*s)
 return out
def verify(dat):
 W=dat['weights']
 if len(W)!=133 or any(type(v)is not int or v<0 for v in W):raise ValueError('bad charge vector')
 T=[Template(x)for x in dat['templates']]
 rules={}
 for parts,k,mp,v in dat['certificates']:
  p=tuple(parts)
  if p in rules or list(p)!=sorted(p):raise ValueError('duplicate or unordered shape')
  sizes=sorted(set(p));mult=[p.count(x)for x in sizes]
  if len(mp)!=len(v) or len(v)!=len(sizes) or not 0<=k<len(T):raise ValueError('bad shape maps')
  if any(type(i)is not int or not 0<=i<T[k].N for i in mp) or any(type(i)is not int or i<0 for i in v):raise ValueError('invalid transfer indices')
  cap=T[k].check(sizes,mult,mp,v,W)
  if not cap<0:raise ArithmeticError(('nonnegative bound',p,cap))
  rules[p]=cap
 used=set()
 for N,m,count in dat['targets']:
  if not 0<m<=N//2 or N>132:raise ValueError('invalid target')
  bad=residual(W,N,m)
  if len(bad)!=count or not bad<=set(rules):raise RuntimeError(('incomplete barrier certificate',N,count,len(bad),bad-set(rules)))
  used|=bad
  print('PASS',N,'points:',m,'strict disjoint pairs;',len(bad),'residual shapes')
 if used!=set(rules):raise ValueError('unreferenced shape')
 print('PASS all residual shapes, integer Gram factors and continuous scalar bounds:',len(rules))
if __name__=='__main__':
 js=Path(__file__).with_name('kissing-component-harmonic-data.json')
 verify(json.loads(js.read_text()))
