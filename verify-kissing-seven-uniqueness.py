#!/usr/bin/env python3
"""Exact independent checker for the 125-point isoradial bound and the U3(3) D8 witness.
All matrix arithmetic and polynomial inequalities are integral/rational.
"""
from pathlib import Path
import sys
if not __debug__:raise RuntimeError("assertions required")
from fractions import Fraction as F
from math import factorial,comb,lcm
from functools import lru_cache
import json
def rf(x,k):
 r=F(1)
 for s in range(k):r*=x+s
 return r
@lru_cache(None)
def basis(d,k):
 if not k:return {0:F(1)}
 if d==1:return {1:F(1)}
 v={}
 for j in range(k//2+1):
  a=k-2*j;c=F((-1)**j*2**a, factorial(j)*factorial(a))
  if d==2:c*=F(k*factorial(k-j-1),2)
  else:c*=rf(F(d-2,2),k-j)
  v[a]=c
 S=sum(v.values());return {i:x/S for i,x in v.items()}
def addto(A,B,f):
 for x,v in B.items():A[x]=A.get(x,0)+f*v
def mul(A,B):
 C={}
 for (i,j),a in A.items():
  for (k,h),b in B.items():
   if a*b:C[i+k,j+h]=C.get((i+k,j+h),0)+a*b
 return C
def power(A,k):
 f=[{(0,0):F(1)}]
 for i in range(k):f.append(mul(f[-1],A))
 return f
def regions(r,w):
 cuts=[F(-1),F(1)]
 if w not in (0,1):cuts=sorted({max(F(-1),min(F(1),z)) for z in cuts+[(F(1,2)-j*(1-w))/w for j in (-1,1)]})
 if w==1:cuts=[F(-1),F(1,2)]
 for a,b in ([(F(j),F(j))for j in (-1,1)if w!=1 or j<1] if r==1 else zip(cuts,cuts[1:])):
  top=lambda u:F(1) if w==1 else min(F(1),(F(1,2)-w*u)/(1-w))
  if top((a+b)/2)>=-1:yield a,b,top(a),top(b)
def split(v):
 h=[];l=[];k=len(v)-1
 for i in range(k+1):
  l.append(v[0]<<(k-i));h.append(v[-1]<<(k-i));v=[v[j]+v[j+1] for j in range(len(v)-1)]
 return l,h[::-1]
def tree(B,s=0):
 if min(min(r) for r in B)>=0:return 1
 assert s<26
 tr=len(B)>1 and (len(B[0])==1 or s%2==0)
 X=list(zip(*B)) if tr else B
 LR=[split(R)for R in X];cg=lambda M:list(zip(*M)) if tr else M
 return 1+sum(tree(cg([Z[i] for Z in LR]),s+1)for i in range(2))
def verify(r,a,b,L,weights):
 n=7-r;nodes=0
 if r>1:r,n=n,r;a,b=2**L-b,2**L-a;weights=[(j,i,c)for i,j,c in weights]
 poly={(0,0):-10**7}
 for i,j,c in weights:
  for h,y in basis(r,i).items():
   for k,z in basis(n,j).items():poly[h,k]=poly.get((h,k),0)-c*y*z
 for w in [F(a,2**L),F(b,2**L)]:
  for lo,hi,vlo,vhi in regions(r,w):
   U={(0,0):hi,(1,0):lo-hi};V={(0,0):vhi,(1,0):vlo-vhi,(0,1):-1-vhi,(1,1):vhi-vlo}
   X=power(U,max(x for x,y in poly));Y=power(V,max(y for x,y in poly));W={}
   for (i,j),v in poly.items():addto(W,mul(X[i],Y[j]),v)
   nm=max(x for x,y in W);nn=max(y for x,y in W);B=[]
   for k in range(nm+1):
    B.append([sum(v*F(comb(k,i),comb(nm,i))*F(comb(h,j),comb(nn,j))for (i,j),v in W.items()if i<=k and j<=h) for h in range(nn+1)])
   den=lcm(*(v.denominator for row in B for v in row));nodes+=tree([[int(t*den)for t in row] for row in B])
 return nodes

def group_witness():
    # Standard 7a integer generators from the ATLAS of Group Representations:
    # https://brauer.maths.qmul.ac.uk/Atlas/exc/G22/gap0/U33G1-Zr7aB0.g
    A=[[-1,0,0,0,0,0,0],[0,-1,0,0,0,0,0],[0,1,0,0,0,1,0],[-1,0,0,0,0,0,1],
       [0,0,0,0,1,0,0],[0,1,1,0,0,0,0],[-1,0,0,1,0,0,0]]
    B=[[0,-1,0,0,0,-1,0],[0,1,1,0,0,0,0],[0,-1,0,0,0,0,0],[1,0,0,0,0,0,0],
       [0,0,0,0,0,0,-1],[0,0,0,-1,0,0,1],[0,0,0,0,1,0,1]]
    def mat(X,Y):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*Y)] for row in X]
    I=[[int(i==j) for j in range(7)] for i in range(7)]
    D=mat(B,mat(B,B));R=mat(A,D);R2=mat(R,R)
    assert mat(A,A)==mat(D,D)==mat(R2,R2)==I and R2!=I
    L=[I,R,R2,mat(R2,R)];H=L+[mat(A,X) for X in L]
    assert len({tuple(map(tuple,X)) for X in H})==8
    assert all(sum(X[i][j] for X in H)==0 for i in range(7) for j in range(7))
    print("U3(3): order-eight subgroup has zero averaging matrix.")

def check(rows):
    assert all(isinstance(row,list) and len(row)==5 for row in rows)
    for r,a,b,L,chart in rows:
        assert all(type(x) is int for x in (r,a,b,L)) and r in (1,2,3) and L>=0 and 0<=a<b<=2**L
        assert chart and all(type(i) is type(j) is type(c) is int and i>=0 and j>=0 and
            0<i+j<=10 and (r!=1 or i<=1) and c>0 for i,j,c in chart)
        assert 10**7+sum(c for i,j,c in chart)<126*10**7
    for r in (1,2,3):
        spans=sorted((F(a,2**L),F(b,2**L)) for d,a,b,L,ch in rows if d==r)
        assert spans and spans[0][0]==0 and spans[-1][1]==1 and all(s[1]==t[0] for s,t in zip(spans,spans[1:]))
    print("Verified",len(rows),"closed radius charts in",sum(verify(*row) for row in rows),"Bernstein nodes.")
if __name__=="__main__":
    group_witness()
    check(json.loads((Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name("kissing-seven-uniqueness-charts.json")).read_text()))
