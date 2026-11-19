#!/usr/bin/env python3
"""Exact finite samples, arbitrary-host pair inequalities and the complete cycle table; companion to verify.py."""
from verify import *
from collections import Counter
def sigr(A):
 from math import lcm
 d=lcm(*(F(a).denominator for r in A for a in r)) if A else 1
 return sig([[int(d*a) for a in r] for r in A])
def plus(H,u,v,c):
 n=len(H)
 return [[H[i][j]+c*u[i]*v[j] for j in range(n)] for i in range(n)]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def restrict(H,w):
 n=len(w);i=next((i for i in range(n) if w[i]),None)
 if i is None:return H
 z=[]
 for j in range(n):
  if i==j:continue
  v=[0]*n;v[j]=w[i];v[i]=-w[j];z.append(v)
 return [[sum(x*dot(r,b) for x,r in zip(a,H)) for b in z] for a in z]
def checkpair():
 rng=Random(520);ct=0
 for c,d in [(1,1),(1,3),(3,1),(3,3)]:
  a={1:F(2,3),3:F(4)}[c];b={1:F(2,3),3:F(4)}[d]
  for e in [-1,1]:
   for _ in range(100):
    n=4;H=[[0]*n for i in range(n)]
    for i in range(n):
     for j in range(i+1):H[i][j]=H[j][i]=rng.randrange(-4,5)
    u=[rng.randrange(-2,3) for _ in range(n)];v=[rng.randrange(-2,3) for _ in range(n)]
    if _%5==0:v=u[:]
    if _%7==0:v=[0]*n
    A=[r+[x,y] for r,x,y in zip(H,u,v)]+[u+[a,e],v+[e,b]]
    if (c,d)==(1,1):U=restrict(H,[y-e*x for x,y in zip(u,v)])
    elif (c,d)==(3,3):U=restrict(H,[y-x for x,y in zip(u,v)])
    else:U=plus(plus(H,u,v,e),v,u,e)
    req("pair over signed odd gap",2*sigr(A)-c-d<=2*sigr(U))
    # even gap: z2=e z1
    w=[x+e*y for x,y in zip(u,v)]
    A=[r+[x] for r,x in zip(H,w)]+[w+[a+b]]
    if (c,d)==(1,1):U=plus(plus(H,u,v,-e),v,u,-e)
    else:U=restrict(H,w)
    req("pair over even gap",2*sigr(A)-c-d<=2*sigr(U));ct+=2
 print("PASS pair-erasing comparisons against integer hosts, signed and coincident ports:",ct)
def states():
 ymin={0:F(0),1:F(2,3),2:F(2),3:F(4)};out={};bad=[]
 for (c,y),a,b in product([(1,F(2,3)),(3,F(4))],range(4),range(4)):
  k=sum((1 if l==1 else -1 if l==3 else 0) for l in (a,b))
  z=set((1 if l==0 else -1) for l in (a,b) if not l%2)
  if len(z)==2: sg=0;g=F(0)
  elif z:
   s=z.pop();v=1+y+2*k*s;sg=(v>0)-(v<0);g=1/v if v else None
  else:
   det=y-k*k;sg=2 if det>0 else 0 if det<0 else 1;g=y/det if det else None
  C=3+c-2*sg
  if g is None:req("singular state discard",C>=2);bad.append((c,a,b,C))
  else:
   out[C]=min(out.get(C,g),g)
   req("finite state closed",C>=0 and (C>=4 or 1-g<=ymin[C]))
 req("table",out=={0:F(1),2:F(3,11),4:F(-1,5),6:F(-3)})
 req("singular",bad==[(3,1,1,4),(3,3,3,4)])
 print("PASS all 32 rational marked-cycle configurations and two incompatible cases")
def raw():
 rng=Random(34345);cnt=0
 for j in range(600):
  n=1;E=[];c=0
  for _ in range(rng.randrange(1,12)):
   p=rng.randrange(n)
   if rng.randrange(3)==0:E.append((p,n));n+=1
   else:
    ell=rng.randrange(3,9);l=[p,*range(n,n+ell-1),p];n+=ell-1
    E.extend(zip(l,l[1:]));c+=1
  req("cactus direct",2*sig(mat(n,E))<=3*c-1);cnt+=1
 print("PASS directly assembled cacti of unrestricted block shape, deterministic samples:",cnt)
if __name__=='__main__':states();checkpair();raw()
