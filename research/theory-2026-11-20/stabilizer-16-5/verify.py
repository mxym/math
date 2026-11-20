"""Exact certificate checker. No optimizer or third-party source/census is consulted."""
from itertools import product
from math import comb
from collections import Counter
from functools import cache
import json
from pathlib import Path
assert __debug__
N=16;R=2048
@cache
def kr(n,j,i):
 return sum((-1)**t*3**(j-t)*comb(i,t)*comb(n-i,j-t) for t in range(j+1)if t<=i and j-t<=n-i)
@cache
def local(w,a,b):
 # 0=I,1=X,2=Z,3=Y. Reference all Z. Evaluate the complete character sum directly, not via its generating polynomial.
 c=[1]*a+[2]*b+[0]*(w-a-b);r=Counter()
 for t in product(range(4),repeat=w):
  e=sum(1 for i,j in zip(c,t)if i and j and i!=j)
  r[sum(j in (1,3)for j in t),t.count(2)]+=(-1)**e
 return r
def systems(w):
 if not w:
  v=[0,*range(9,16)];eye=[[int(i==j)for i in v]for j in range(17)]
  k=[[kr(16,j,i)for i in v]for j in range(17)]
  b=[[u-R*z for u,z in zip(x,y)]for x,y in zip(k,eye)]
  sh=[[x*(-1)**j for x,j in zip(z,v)]for z in k]
  return [eye[0],[1]*len(v),*b[1:5]],[1,R,0,0,0,0],b[5:]+sh
 v=[(a,b,j)for a in range(0,w+1,2)for b in range(w-a+1)for j in range(N-w+1)if b<=w-a-b]
 t=[(a,b,j)for a in range(w+1)for b in range(w-a+1)for j in range(N-w+1)]
 eq=[];ge=[];sh=[];L=[]
 for aa,bb,jj in t:
  lv=[];gv=[];sv=[]
  for a,b,j in v:
   l=g=s=0
   for h in {b,w-a-b}:
    k=local(w,a,h)[aa,bb]*kr(N-w,jj,j)
    l+=int((a,h,j)==(aa,bb,jj));g+=k;s+=(-1)**(a+h+j)*k
   lv.append(l);gv.append(g-R*l);sv.append(s)
  L.append(lv);ge.append(gv);sh.append(sv)
  if 1<=aa+bb+jj<=4:eq.append(gv)
 return [L[0],list(map(sum,zip(*L))),*eq],[1,R]+[0]*len(eq),ge+sh
for w in range(5):
 E,f,G=systems(w);m=len(E[0]);lhs=[0]*m;rhs=0
 c=json.loads(Path(f'cert{w}.json').read_text());assert c['w']==w
 for tag,i,z in c['terms']:
  assert type(i)==type(z)==int and i>=0
  if tag=='eq':r=E[i];rhs+=z*f[i]
  elif tag=='ge':assert z>=0;r=G[i]
  else:assert tag=='v'and i<m and z>=0;r=[int(h==i)for h in range(m)]
  lhs=[h+z*p for h,p in zip(lhs,r)]
 assert lhs==[0]*m and rhs==c['rhs']>0
 print(f'PASS {w}: zero left-hand side >= {rhs} contradiction.',flush=True)
