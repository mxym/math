#!/usr/bin/env python3
"""Exact rational continuous simplex-belt bound; Python standard library only."""
import math,itertools as it
from fractions import Fraction as Q
from math import comb,isqrt
import sys
if not __debug__:raise RuntimeError("assertions required")
def sc(a,s):return [Q(x)*s for x in a]
def add(a,b):return [Q(x)+y for x,y in zip(a+[0]*max(0,len(b)-len(a)),b+[0]*max(0,len(a)-len(b)))]
def ev(p,x):return sum(q*x**i for i,q in enumerate(p))
def sec(p,x):return sum(q*x**(i//2)for i,q in enumerate(p)if i%2==0)
def solver(A,b):
 T=[list(a)+[v]for a,v in zip(A,b)]
 for j in range(4):
  t=next(i for i in range(j,4) if T[i][j]);T[t],T[j]=T[j],T[t];z=T[j][j];T[j]=[a/z for a in T[j]]
  for i in range(4):
   if i==j:continue
   u=T[i][j];T[i]=[a-u*b for a,b in zip(T[i],T[j])]
 return [row[-1]for row in T]
def coefs(n,M,aa,bb):
 d=n-1;al={k:Q(v,1000)for k,v in aa.items()};al[0]=Q(999,1000)
 bb={k:[Q(t,1000)for t in T]for k,T in bb.items()}
 P=[[Q(1)],[Q(0),Q(1)]]
 while len(P)<=max(al):
  k=len(P)-1;P.append(sc(add(sc([0]+P[-1],2*k+d-2),sc(P[-2],-k)),Q(1,k+d-2)))
 # Bernstein coefficients of f under t=-1+3z/2. Bisect until all are negative.
 f=[Q(0)]*(1+max(al))
 for k,a in al.items():f=add(f,sc(P[k],a))
 m=len(f)-1
 u=[sum(f[k]*comb(k,j)*(-1)**(k-j)*Q(3,2)**j for k in range(j,m+1))for j in range(m+1)]
 bez=[sum(u[j]*Q(comb(i,j),comb(m,j)) for j in range(i+1))for i in range(m+1)]
 def neg(v,j=0):
  if max(v)<=0:return 1
  assert j<24
  a=[v[0]];b=[v[-1]]
  while len(v)>1:
   v=[(x+y)/2 for x,y in zip(v,v[1:])];a.append(v[0]);b.append(v[-1])
  return 1+neg(a,j+1)+neg(b[::-1],j+1)
 nodes=neg(bez);assert min(al.values())>0
 def ref(y,k):
  p=P[k];ss=sum(t*t for t in y);out=[]
  for j in range(1,n//2+1):
   w=[sec(p,Q(n*sum(y[i]for i in T)**2,ss*j*(n-j))) for T in it.combinations(range(n),j)]
   out.append(sum(w)/len(w))
  w=[sec(p,Q((y[i]-y[j])**2,2*ss))for i,j in it.combinations(range(n),2)]
  return out+[sum(w)/len(w)]
 roots=[[n-j]*j+[-j]*(n-j)for j in range(1,n//2+1)]+[[1,-1]+[0]*(n-2)]
 off=al[0]-sum(al.values())/M
 for k,b in bb.items():
  C=[ref(v,k)for v in roots]
  off-=al[k]*sum(x*y*c for x,row in zip(b,C)for y,c in zip(b,row))
 def evalY(y):
  V=off
  for k,b in bb.items():V+=2*al[k]*sum(x*z for x,z in zip(b,ref(y,k)))
  scale=Q(4*n,d*sum(i*i for i in y))
  return [Q(1),sum(i**4 for i in y)*scale**2,sum(i**6 for i in y)*scale**3,sum(i**3 for i in y)**2*scale**3],V
 from random import Random
 r=Random(84);rows=[];V=[]
 for i in range(9):
  y=[r.randrange(-5,6)for i in range(n-1)];y.append(-sum(y));row,v=evalY(y);rows.append(row);V.append(v)
 z=solver(rows[:4],V[:4]);assert all(sum(a*b for a,b in zip(z,row))==v for row,v in zip(rows,V))
 print("scalar signs",n,M,nodes)
 return [math.floor(x*100000)for x in z]
DATA=[
 (7,59,{1: 5235, 2: 13163, 3: 20718, 4: 21803, 5: 14778, 6: 5176, 9: 842, 10: 430}, {4: [-225, 27, 90, -97], 6: [136, -156, 105, -7]}),
 (8,115,{1: 6244, 2: 18197, 3: 32496, 4: 38264, 5: 28850, 6: 11141, 9: 2709, 10: 1698}, {4: [-138, 0, 39, 48, -60], 6: [36, -27, 8, 20, -2]})]

def ceilingsqrt(z):
 if z<=0:return 0
 v=isqrt(z);return v+(v*v!=z)
def boxes(n,M,W,alternate):
 d=n-1;S=3584 if alternate else 4096;S2=S*S;R=(192 if alternate else 256)*d;T=1024
 U=4*n*R//d;N=4*n*S2;off,b,c,e=W
 qmax=-(-(S+1)**2*R//S2)
 assert c>0 and b<0 and e<0 and b+3*c*Q(qmax,R)<0
 ct=dep=0
 for p in range((n+1)//2,n):
  def dfs(l,u,z):
   nonlocal ct,dep
   ct+=1;dep=max(z,dep)
   for it0 in range(2):
    for i in reversed(range(n-1)):
     if i!=p-1:l[i]=max(l[i],l[i+1])
    for i in range(1,n):
     if i!=p:u[i]=min(u[i],u[i-1])
    if any(x>y for x,y in zip(l,u)):return
    lo=sum(l[:p])-sum(u[p:]);hi=sum(u[:p])-sum(l[p:]);ql=sum(x*x for x in l);qh=sum(x*x for x in u)
    if lo>0 or hi<0 or d*ql>N or d*qh<N:return
    for i in range(n):
     a,v=l[i],u[i]
     if i<p:l[i],u[i]=max(a,v-hi),min(v,a-lo)
     else:l[i],u[i]=max(a,v+lo),min(v,a+hi)
     l[i]=max(l[i],isqrt(max(0,N//d-qh+v*v)))
     u[i]=min(u[i],ceilingsqrt(max(0,-(-N//d)-ql+a*a)))
     if l[i]>u[i]:return
   val=off;rem=U;bins=[]
   for x,y in zip(l,u):
    a=x*x*R//S2;v=-(-y*y*R//S2)
    val+=(b*R+c*a)*a*a//(R**3)
    slope=(b*(a+v)*R+c*(a*a+a*v+v*v))//(R*R)
    bins.append((slope,v-a));rem-=a
   if rem<0:return
   v0=0
   for slope,w in sorted(bins):
    amount=min(w,rem);v0+=slope*amount;rem-=amount
   if rem:return
   val+=v0//R
   bounds=[]
   for j in range(6):
    a=v=0
    for i,(x,y) in enumerate(zip(l,u)):
     xl=2*x**3-j*x*S2;yl=2*y**3-j*y*S2
     low=min(xl,yl);high=max(xl,yl)
     if 6*x*x<j*S2<6*y*y:low=xl+(6*x*x-j*S2)*(y-x)
     a+=low if i<p else -high;v+=high if i<p else -low
    bounds.append(-(-T*max(abs(a),abs(v))//(2*S**3)))
   t=min(bounds)
   if val+e*t*t//(T*T)>0:return
   inds=range(n-1,-1,-1) if alternate else range(n);j=max(inds,key=lambda i:u[i]-l[i])
   assert u[j]-l[j]>=2 and z<64,("unresolved",n,l,u)
   mid=(l[j]+u[j])//2;ll=l[:];uu=u[:];ll[j]=uu[j]=mid
   dfs(l[:],uu,z+1);dfs(ll,u[:],z+1)
  dfs([0]*n,[S+1]*n,0)
 print("simplex vertices",n,"excluded size",M,"round-down",W,"nodes",ct,"max depth",dep)
for n,M,al,bb in DATA:
 W=coefs(n,M,al,bb)
 for alternate in (False,True):boxes(n,M,W,alternate)
