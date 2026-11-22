#!/usr/bin/env python3
"""Outward ordinary weights and fixed-target weighted intersection sums."""
from fractions import Fraction as F
from math import isqrt,comb,ceil,floor
S=10**12
a=F(".110");theta=F(".499");G=500;Q=1000
def require(ok):
 if not ok:raise ArithmeticError('tagged negative credit certificate failed')
def ceilq(a,b): return (a+b-1)//b
# rho2(u)/u interval differences, with exact lower primitive on each tile.
def rho_integral(K=20000):
 n=4*K;hi=[S]*(K+1);lo=hi.copy()
 for i in range(K,n):
  lo.append(max(0,lo[i]-ceilq(2*(i+1-K)*hi[i-K],i*i)))
  hi.append(max(0,hi[i]-2*(i-K)*lo[i+1-K]//((i+1)**2)))
  require(lo[-1]<=hi[-1])
 I=[0]
 for i in range(n):I.append(I[-1]+(2*i+1)*lo[i+1])
 return I,K
RI,K=rho_integral()
J=[[S]*9001]
for j in range(2,4):
 row=[0]*9001
 for h in range(1001,9001):
  row[h]=row[h-1]+J[-1][h-1001]//h
 J.append(row)
def sqrt(x,up):
 n,d=x.numerator,x.denominator
 p=isqrt(n*S*S//d)
 return F(p+(up and p*p*d!=n*S*S),S)
def loglo(x):
 q=(x-1)/(x+1)
 return 2*sum(q**(2*j+1)/(2*j+1) for j in range(20))
def pc(x):return floor(x*S)
def w3(u,v):
 return -sum(c*sum(F(comb(k,j),(j+1)*(k-j+1))*u**j*v**(k-j)
                    for j in range(k+1))
             for k,c in enumerate([-78,1152,-4512,6720,-3360]))
def w5(T,Tp,q0):
 lo=None
 for j in range(floor(T*Q/3),ceil((Tp-2*a)*Q)+1):
  l=F(j,Q);r=l+F(1,Q)
  t=T-r;v=min(t/2,max(a,T-2*r))
  q=q0+l*l+t*t/2
  w=(40320*sqrt(q/24,False)-1056*sqrt(2/q,True))*l*v*(t-v)
  if lo is None or w<lo:lo=w
 return lo
cells=[]
for i in range(3,58):
 u=F(i+1,G);ul=F(i,G)
 for j in range(i+1,65):
  v=F(j+1,G);vl=F(j,G)
  s=u+v
  if ul+vl<=F(".065") or s>F(".170") or v>=a:continue
  T=1-s;Tp=1-ul-vl
  require(T>F(".5") and T>3*a)
  q0=ul*ul+vl*vl
  A4=1680*(q0+T*T)-528
  V1=a*(T-a);V2=Tp*Tp/4
  W4=min(V1*(A4-3360*V1),V2*(A4-3360*V2))
  W=[w3(u,v),W4,w5(T,Tp,q0)]
  require(min(W)>0)
  WL=[pc(w-F(1,10**6)) for w in W]
  ix=sorted(range(3),key=lambda k:WL[k])
  dh=[WL[ix[0]],WL[ix[1]]-WL[ix[0]],WL[ix[2]]-WL[ix[1]]]
  x=floor((T/a-1)*Q)
  bodies=[pc(F(row[x],S)/Tp) for row in J]
  m=[sum(bodies[i] for i in ix[t:]) for t in range(3)]
  D=theta-s
  require(2<D/a<4)
  k=pc(2/D*loglo(D/a-1))
  cells.append((int(G*s),k,dh,m))
cache={}
def ambient(ss):
 if ss not in cache:
  u=theta*(1-F(ss,G))/a
  h=floor(K*u)
  C=2*K*K*S/(a*a*RI[h])
  cache[ss]=ceil(C*S)
 return cache[ss]
Ans=0
for u,k,d,m in cells:
 for v,k2,d2,m2 in cells:
  C=ambient(u+v)*S
  for i in range(3):
   for j in range(3):
    Ans+=max(0,k*m2[j]+k2*m[i]-C)*d[i]*d2[j]
res=F(Ans,S**4*G**4)
require(len(cells)==961 and res>F(".156"))
print('distinct tag boxes',len(cells),'rho2 caps',len(cache),'positive signed block lower',float(res))
