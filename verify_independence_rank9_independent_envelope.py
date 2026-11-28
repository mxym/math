#!/usr/bin/env python3
"""Alternative phase-tagged envelope for rank 9 at order 18; no repository imports."""
from itertools import combinations_with_replacement,combinations,product
from math import comb
import numpy as np
def need(x,msg):
 if not x:raise RuntimeError(msg)
def choose(a,b):return comb(a,b) if 0<=b<=a else 0
def ceil(a,b):return -((-a)//b)
# Colored complex: one choice absent/first/second in each of the nine residues.
faces=[[]for _ in range(10)]
for t in product((0,1,2),repeat=9):
 S=sum(1<<(j+(a-1)*9)for j,a in enumerate(t)if a);faces[sum(i!=0 for i in t)].append(S)
for t in faces:t.sort()
U={}
for k in range(2,9):
 ranks={s:i+1 for i,s in enumerate(faces[k])}
 U[k]=np.cumsum(np.bincount([ranks[s&(s-1)] for s in faces[k+1]],minlength=len(faces[k])+1))
M=len(faces[2]);lb=np.full((M+1,10),100000,dtype=int)
# For each exterior edge count and sorted K-degrees, form prefix sums for
# all ranks independently, then pool componentwise minima by TOTAL edge count.
for ds in combinations_with_replacement(range(9),9):
 begin=36+sum(ds)
 if begin>M:continue
 u=sorted(max(0,a+b-9)for a,b in combinations(ds,2))
 ne=min(len(u),M-begin)
 get=np.array([[choose(9,k)+sum(choose(d,k-1)for d in ds) for k in range(3,10)]]+[[choose(t,k-2)for k in range(3,10)]for t in u[:ne]],dtype=int)
 Z=np.cumsum(get,axis=0);v=np.arange(ne+1);Z[:,0]+=np.maximum(0,-((-(4*v*v-81*v))//27));m=v+begin
 Z[:,0]=np.maximum(Z[:,0],-((-(4*m*m-324*m))//54))
 lb[begin:begin+ne+1,3:10]=np.minimum(lb[begin:begin+ne+1,3:10],Z)
# phase 0: no drop, 1: drop with no subsequent rise, 2..8: first rise from k to k+1.
res={};sl=set()
for m in range(36,M+1):
 states=[np.zeros(len(faces[2])+1,dtype=int) for _ in range(9)];states[0][m]=18
 for k in range(2,9):
  nxt=[np.zeros(len(faces[k+1])+1,dtype=int) for _ in states]
  for ph,col in enumerate(states):
   for yy in np.flatnonzero(col):
    y=int(yy);x=int(col[y]);L=max(1,int(lb[m,k+1]),ceil(k*k*y*y-18*y*x,(k*k-1)*x));R=int(U[k][y])
    if L>R:continue
    bins=[(L,min(R,y-1),1 if ph==0 else ph),(max(L,y),min(R,y),ph),(max(y+1,L),R,k if ph==1 else ph)]
    for a,b,h in bins:
     if a<=b:nxt[h][a:b+1]=np.maximum(nxt[h][a:b+1],y)
  states=nxt
 rr={h for h in range(2,9)if np.any(states[h])}
 if rr:res[m]=rr;sl|=rr
need(sl=={4} and sorted(res)==list(range(62,120)),'envelope')
print('PASS independent full-path envelope: first post-drop rise only 4 -> 5; edge counts 62 through 119')
