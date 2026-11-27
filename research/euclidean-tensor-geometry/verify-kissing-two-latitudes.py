#!/usr/bin/env python3
"""Exact two-latitude matrix LP certificate; only the Python standard library."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb,gcd,lcm
from pathlib import Path
import json,zlib,base64,sys
if not __debug__:raise RuntimeError("assertions required")
S=F(4001,8000);den=10**7;K=10
@lru_cache(None)
def basis(dim):
 p=[[F(1)],[F(-1),F(1)]]
 for k in range(1,K):
  t=p[-1];a=[F(0)]*(k+2)
  for j,c in enumerate(t):a[j]-=(2*k+dim-2)*c;a[j+1]+=(2*k+dim-2)*c
  for j,c in enumerate(p[-2]):a[j]-=k*c
  p.append([x/(k+dim-2)for x in a])
 M=lcm(*(c.denominator for row in p for c in row))
 return [[int(M*c)for c in row]+[0]*(K+1-len(row))for row in p]
def poly(n,coef):
 B=basis(n-1)
 return prim(tuple(-sum(coef[j]*B[j][i]for j in range(K+1))for i in range(K+1)))
def prim(z):
 g=gcd(*z)
 return tuple(x//g for x in z) if g>1 else tuple(z)
def splitb(P):
 d=len(P)-1;L=[];R=[]
 for j in range(d+1):
  L.append(P[0]<<(d-j));R.append(P[-1]<<(d-j));P=[x+y for x,y in zip(P,P[1:])]
 return L,R[::-1]
def pos(B,depth=0):
 if min(B)>=0:return True
 if B[0]<0 or B[-1]<0 or depth>=18:return False
 a,b=splitb(B);return pos(a,depth+1) and pos(b,depth+1)
bc=[[comb(k,j)for j in range(k+1)]for k in range(K+1)]
mult=lcm(*bc[K]);factor=[mult//t for t in bc[K]]
@lru_cache(maxsize=15000)
def coeff(cut):
 c=min(cut,F(1))+1
 return [c.numerator**j*c.denominator**(K-j)*factor[j]for j in range(K+1)]
@lru_cache(maxsize=150000)
def cert(P,cut):
 if cut< -1:return True
 V=[x*y for x,y in zip(P,coeff(cut))]
 return pos([sum(x*y for x,y in zip(V,row))for row in bc])
@lru_cache(None)
def height(z):return 2*z/(1+z*z),(1-z*z)/(1+z*z)
def same(z):
 h,r=height(z);return (S-h*h)/(r*r)
def cross(y,z):
 h,r=height(y);k,t=height(z)
 return min(F(1),(S+h*k)/(r*t))
def sumc(a,b):return tuple(x+y for x,y in zip(a,b))
def pad(a):return tuple(x*2 for x in a)
def node(T,U,typ,e=0):
 # Four corner polynomials share a positive scalar: interpolation is literal.
 a,b,c,d=T
 t=same(a) if typ==0 else same(c) if typ==2 else cross(b,d)
 if all(cert(prim(q),t)for q in U):return 1
 assert e<28,("unresolved radial box",typ,T,e)
 u,v,w,x=U
 if typ==0 or (typ==1 and ((e%2==1) if "--sturm" in sys.argv else (cross(b,d)-cross(a,d)>=cross(b,d)-cross(b,c)))):
  p=(a+b)/2;y=sumc(u,w);z=sumc(v,x)
  return 1+node((a,p,c,d),(pad(u),pad(v),y,z),typ,e+1)+node((p,b,c,d),(y,z,pad(w),pad(x)),typ,e+1)
 else:
  p=(c+d)/2;y=sumc(u,v);z=sumc(w,x)
  return 1+node((a,b,c,p),(pad(u),y,pad(w),z),typ,e+1)+node((a,b,p,d),(y,pad(v),z,pad(x)),typ,e+1)
def rawpoly(n,coef):
 B=basis(n-1)
 return tuple(-sum(coef[j]*B[j][i]for j in range(K+1))for i in range(K+1))
def check(n,dat,verbose=False):
 N={6:72,7:124}[n]
 full,small=dat["one"]
 for j,A in enumerate([full,small]):
  assert len(A)==K and all(type(x)is int and x>=0 for x in A)
  assert cert(poly(n,[den,*A]),S if not j else same(F(9,32)))
 assert (den+sum(full))//den+(den+sum(small))//den<N
 leaf,V=json.loads(zlib.decompress(base64.b64decode(''.join(dat["atlas"]),validate=True)))
 assert leaf and V
 P=[]
 for A in V:
  assert len(A)==K+1 and all(len(row)==3 and all(type(x)is int for x in row)for row in A)
  assert all(i>=0 and k>=0 and i*k>=j*j for i,j,k in A)
  assert all(den+sum(row[e]for row in A)<N*den for e in (0,2))
  P.append([rawpoly(n,[row[e]+(den if i==0 else 0)for i,row in enumerate(A)]) for e in range(3)])
 leaves={tuple(r[:5]):r[5]for r in leaf};assert len(leaves)==len(leaf)
 seen=set()
 def covering(a,b,c,d,L):
  if a>=d:return
  key=(a,b,c,d,L)
  if key in leaves:seen.add(key);return
  assert L<19
  for i,j in [(2*a,a+b),(a+b,2*b)]:
   for k,l in [(2*c,c+d),(c+d,2*d)]:covering(i,j,k,l,L+1)
 covering(0,9,0,9,5);assert seen==leaves.keys()
 nodes=0
 for num,(a,b,c,d,L,ids) in enumerate(leaf):
  assert len(ids)==4 and all(type(i)is int and 0<=i<len(P)for i in ids)
  T=tuple(F(x,2**L)for x in [a,b,c,d])
  for k in range(3):nodes+=node(T,[P[i][k]for i in ids],k)
  if verbose and num%40==0:print("chart",n,num,"nodes",nodes,flush=True)
 print("Verified dimension",n,":",len(leaf),"patches,",len(V),"vertices,",nodes,"radial nodes; upper",N-1,flush=True)
if "--sturm" in sys.argv:
 @lru_cache(None)
 def basis(dim):
  from math import factorial
  def rising(x,k):return prod2(x+i for i in range(k))
  def prod2(it):
   a=F(1)
   for x in it:a*=x
   return a
  p=[]
  for k in range(K+1):
   c=[F(0)]*(k+1)
   for j in range(k//2+1):
    h=k-2*j;c[h]=F((-1)**j*2**h,factorial(j)*factorial(h))*rising(F(dim-2,2),k-j)
   total=sum(c)
   p.append([sum(c[i]*comb(i,h)*(-1)**(i-h)for i in range(h,k+1))/total for h in range(k+1)])
  M=lcm(*(v.denominator for row in p for v in row));return [[int(M*v)for v in row]+[0]*(K+1-len(row))for row in p]
 def trim(p):
  p=list(p)
  while p and not p[-1]:p.pop()
  return tuple(p)
 def sturm(P):
  a=trim(P);b=trim(tuple(i*t for i,t in enumerate(a))[1:]);r=[a]
  if not b:return r
  r.append(b)
  while b:
   q=a
   while len(q)>=len(b):
    h=len(q)-len(b);s=b[-1];l=q[-1]*(1 if s>0 else -1);aabs=abs(s)
    q=trim(prim(tuple(aabs*x-(l*b[i-h] if i>=h else 0)for i,x in enumerate(q))))
   if not q:break
   q=tuple(-x for x in q);r.append(q);a,b=b,q
  return r
 @lru_cache(maxsize=40000)
 def chain(P):return sturm(P)
 def changes(vals):
  sign=[t>0 for t in vals if t];return sum(i!=j for i,j in zip(sign,sign[1:]))
 @lru_cache(maxsize=40000)
 def cert(P,cut):
  if cut< -1:return True
  T=min(F(1),cut)+1
  if P[0]<=0:return False
  c=chain(P);C,D=T.numerator,T.denominator
  powers=[C**i*D**(K-i) for i in range(K+1)]
  V=[sum(a*b for a,b in zip(r,powers))for r in c]
  return V[0]>0 and changes(r[0]for r in c)==changes(V)
if __name__=="__main__":
 d=json.loads(Path(__file__).with_name("kissing-two-latitude-certificates.json").read_text())
 for n in [6,7]:check(n,d[str(n)])
