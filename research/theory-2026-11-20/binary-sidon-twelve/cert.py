from itertools import combinations,product
from math import prod,gcd,ceil
from functools import reduce
from operator import xor
import numpy as np
from scipy.optimize import linprog
import json
Q=1024
def make(A,m,j,g):
 n=sum(A);R=2*m-n;even=[i for i in range(4)if not A[i]%2]
 assert g is None or len(g)==len(even)
 rank=max(g, default=0).bit_length()if g is not None else 0
 # Character profiles use Walsh magnitudes and product sign.
 flags=[];coef=[];labs=[];rhs=[];sides=[]
 def rows(u,k,leading=False):
  # On the RHS, rows hold total expectations (all Q characters); u is the profile at zero.
  ev=[Q if leading else 1]
  ev+= [Q*a if leading else v*v for a,v in zip(A,u)]
  ev+= [Q*(3*a*a-2*a) if leading else v**4 for a,v in zip(A,u)]
  ev+=[Q*A[i]*A[h]if leading else (u[i]*u[h])**2 for i,h in combinations(range(4),2)]
  ev+=[0 if leading else prod(u)*k]
  if g is None:return ev
  # Work in order of characters on the span G: first add all Q/|G| counts; then each nonzero direction's lower, upper, aggregate second-moment bounds.
  parity=tuple(((A[i]-u[i])//2)%2 for i in even)
  ev+=[Q//(2**rank) if leading else int(tuple((t&v).bit_count()%2 for v in g)==parity) for t in range(2**rank)]
  for h in range(1,2**rank):
   mask=next(j for j in range(1,1<<len(g))if reduce(xor,(v for i,v in enumerate(g)if j>>i&1),0)==h)
   sn=1-2*(sum(p for i,p in enumerate(parity) if mask>>i&1)%2)
   for i in range(4):ev.extend([0,2*Q] if leading else [-sn*u[i]**2,sn*u[i]**2])
   ev.append(2*Q if leading else sn*sum(x*x for x in u))
  return ev
 r=rows(A,1,True);at0=rows(A,1);rhs=np.array([v-w for v,w in zip(r,at0)],dtype=np.int64)
 n0=16+(2**rank if g is not None else 0);sides=[0]*n0+[1]*(len(r)-n0)
 for u in product(*(range(a%2,R+1,2)for a in A)):
  if g is not None:
   parity=tuple(((A[i]-u[i])//2)%2 for i in even)
   if not any(tuple((t&v).bit_count()%2 for v in g)==parity for t in range(2**rank)):continue
  if any(u[i]+u[h]>2*j-m for i,h in combinations(range(4),2)if A[i]+A[h]==m):continue
  for k in ([-1,1] if all(u)else [1]):
   if sum(u)-(2*min(u)if k<0 else 0)>R:continue
   flags.append([*u,k]);coef.append(rows(u,k))
 return np.array(coef,dtype=np.int64),rhs,sides,flags
def modes(n):
 def rec(p,rank):
  if len(p)==n:yield p;return
  for v in range(2**rank):yield from rec(p+[v],rank)
  yield from rec(p+[2**rank],rank+1)
 yield from rec([],0)
def solve(A,m,j,g,deep=True):
 mat,rhs,sides,flags=make(A,m,j,g)
 sc=np.maximum(1,np.max(np.abs(mat),axis=0))
 # Positive certificate margin using the intercept to repair rounding.
 p=linprog(rhs/sc,A_ub=-mat/sc,b_ub=np.zeros(len(mat)),bounds=[(0 if h else -1,1)for h in sides],method='highs')
 if not p.success or p.fun>=-1.e-6:return
 for scale in [10**k for k in range(3,14)]:
  v=np.rint(scale*p.x/sc).astype(np.int64).tolist();v[0]-=min(sum(x*y for x,y in zip(row,v)) for row in mat.tolist());d=reduce(gcd,v);v=[x//d for x in v]if d else v
  if sum(x*y for x,y in zip(rhs.tolist(),v))<0:
   assert min(sum(x*y for x,y in zip(row,v))for row in mat.tolist())>=0 and all(x>=0 or not s for x,s in zip(v,sides))
   return v,len(flags)
def get(n):
 qr=[]
 for m in range((n+1)//2,49):
  H=(2*m-n)**2;lo=n%2
  if 4096*(3*n*n-2*n)-n**4-(lo+H)*(4096*n-n*n)+lo*H*4095>0:continue
  for j in range((m+1)//2,35):
   h=(2*j-m)**2;l=m%2
   if 2048*(3*m*m-2*m)-m**4-(l+h)*(2048*m-m*m)+l*h*2047>0:continue
   b=m-j
   for c in range((n-m+1)//2,n-m+1):
    d=n-m-c
    if any(x+y>m for x,y in combinations([j,b,c,d],2)):continue
    qr.append((m,j,[j,b,c,d]))
 return qr
if __name__=='__main__':
 import sys
 n=int(sys.argv[1]);out={};left=[]
 for m,j,A in get(n):
  pair=solve(A,m,j,None)
  if pair:out[str((m,j,A,None))]=pair[0];print(m,j,A,'plain',pair[1],flush=True);continue
  gmax=sum(q%2==0 for q in A);kept=[]
  for g in modes(gmax):
   pair=solve(A,m,j,g)
   if pair:out[str((m,j,A,g))]=pair[0]
   else:kept.append(g)
  print(m,j,A,'left',len(kept),kept[:15],flush=True)
  left += [(m,j,A,g)for g in kept]
 open('cert'+str(n)+'.json','w').write(json.dumps(out))
 open('res'+str(n)+'.json','w').write(json.dumps(left))
