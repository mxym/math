#!/usr/bin/env python3
"""Independent integer transfer-matrix checker for ALL fixed-rank orbital compression.

No optimizer, SymPy, or floating point. Coefficients of u^k t^j in
Trace([[1,u],[1,ut]]^ell) and in lambda_+^r are computed modulo u^(k+1).
For small n,k, exhaustive vertex permutations (by cycle partition) and
k-subsets give an independent reference.
"""
from itertools import combinations
from math import comb
from collections import Counter

def plus(A,B,sgn=1):
 C=dict(A)
 for a,v in B.items():
  C[a]=C.get(a,0)+sgn*v
 return {a:v for a,v in C.items() if v}

def mul(A,B,k):
 C={}
 for (x,y),v in A.items():
  for (z,w),q in B.items():
   if x+z>k or y+w>k:continue
   C[x+z,y+w]=C.get((x+z,y+w),0)+v*q
 return {a:v for a,v in C.items() if v}

def power(A,n,k):
 B={(0,0):1}
 while n:
  if n&1:B=mul(B,A,k)
  n//=2
  if n:A=mul(A,A,k)
 return B

def onevar_add(A,B,sgn=1):
 C=dict(A)
 for i,v in B.items():C[i]=C.get(i,0)+sgn*v
 return {i:v for i,v in C.items() if v}

def onevar_mul(A,B,k):
 C={}
 for i,v in A.items():
  for j,w in B.items():
   if i+j<=k:C[i+j]=C.get(i+j,0)+v*w
 return {i:v for i,v in C.items() if v}

def lambda_positive(k):
 # lambda^2-(1+ut)lambda+u(t-1)=0, lambda(u=0)=1.
 coeff=[{0:1}]
 for j in range(1,k+1):
  p={i+1:v for i,v in coeff[-1].items() if i+1<=k}
  for i in range(1,j):
   p=onevar_add(p,onevar_mul(coeff[i],coeff[j-i],k),-1)
  if j==1:p=onevar_add(p,{1:1,0:-1},-1)
  coeff.append(p)
 return {(i,j):v for i,p in enumerate(coeff) for j,v in p.items()}

def cycle_polynomials(k):
 trace=[{(0,0):2},{(0,0):1,(1,1):1}]
 a={(0,0):1,(1,1):1}
 d={(1,1):1,(1,0):-1}
 for ell in range(2,k+1):
  trace.append(plus(mul(a,trace[-1],k),mul(d,trace[-2],k),-1))
 return trace

def from_short_cycles(n,k,short):
 assert len(short)==k and sum((j+1)*short[j] for j in range(k))<=n
 r=n-sum((j+1)*short[j] for j in range(k))
 assert r==0 or r>=k+1
 tr=cycle_polynomials(k)
 p=power(lambda_positive(k),r,k)
 for ell in range(1,k+1):
  if short[ell-1]:p=mul(p,power(tr[ell],short[ell-1],k),k)
 result=[p.get((k,j),0) for j in range(k+1)]
 assert min(result)>=0 and sum(result)==comb(n,k),(n,k,short,r,result)
 return result

def partitions(n,upper=None):
 if not n:
  yield ()
  return
 if upper is None:upper=n
 for j in range(min(n,upper),0,-1):
  for t in partitions(n-j,j):yield (j,)+t

def action(part):
 arr=[];base=0
 for ell in part:
  arr.extend(base+(j+1)%ell for j in range(ell))
  base+=ell
 return arr

def direct(part,k):
 n=sum(part)
 g=action(part)
 ans=[0]*(k+1)
 for E in combinations(range(n),k):
  im={g[i] for i in E}
  ans[sum(v in im for v in E)]+=1
 return ans

def main():
 for n in range(3,13):
  checks=0
  for part in partitions(n):
   for k in range(1,min(n,6)+1):
    counts=Counter(part)
    short=tuple(counts.get(j,0) for j in range(1,k+1))
    if (r:=n-sum(j*counts.get(j,0) for j in range(1,k+1))) not in (0,) and r<=k:
     raise AssertionError((n,k,part,r))
    A=from_short_cycles(n,k,short)
    B=direct(part,k)
    assert A==B,(n,k,part,A,B)
    checks+=1
  print('PASS integer full-cycle / direct-subset replay n=%d cases=%d'%(n,checks),flush=True)
 print('ALL FIXED-RANK TRANSFER-MATRIX FORMULAS EXACTLY REPLAYED')
if __name__=='__main__':main()
