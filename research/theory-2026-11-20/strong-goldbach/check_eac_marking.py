#!/usr/bin/env python3
"""Finite controls for exact marking, pair charges and two single-mark rows; no floating arithmetic."""
from itertools import combinations
from math import gcd,isqrt,prod
def check(cond,msg):
 if not cond:raise ValueError(msg)
def factor(n):
 a={};d=2
 while d*d<=n:
  while n%d==0:a[d]=a.get(d,0)+1;n//=d
  d+=1
 if n>1:a[n]=1
 return a
def test(U,Q,checkprime, reverse=False):
 F=[factor(u) for u in U];k=len(U)
 check(len(U)==len(Q)==len(set(U))==len(set(Q)) and k>=2,'fixture')
 check(all(set(f)<=set(Q) for f in F),'not factor-closed alphabet')
 if checkprime:check(all(factor(q)=={q:1} for q in Q),'nonprime alphabet')
 D=max(U)-min(U);check(D>0,'diameter')
 assigns={q:max(range(k), key=lambda i:(F[i].get(q,0),-i if reverse else i)) for q in Q}
 V=U.copy();counts=[0]*k
 for q,i in assigns.items():V[i]//=q**F[i].get(q,0);counts[i]+=1
 pairmass=1;shares=1;wc=1;shared_square=1
 for q in Q:
  for a in range(1,1+max(f.get(q,0) for f in F)):
   r=sum(f.get(q,0)>=a for f in F)
   if r<2:continue
   check(q**a<=D,'shared prime power bigger than diameter')
   shares*=q**(r-1);pairmass*=q**(r*(r-1)//2);wc*=q;shared_square*=q**((r-1)**2)
 check(shares==prod(V),'mark-mass mismatch')
 disc=prod(abs(s-t) for s,t in combinations(U,2))
 check(disc%pairmass==0 and wc<=D**k and shared_square<=pairmass**2,'pair or Cauchy controls')
 # Equalities checked for both maximum tie choices. R=exp(E); v_i^k<=R^4 means log(v_i)<=4E/k.
 R=prod(V);singles=[i for i in range(k) if counts[i]==1 and V[i]**k<=R**4]
 low=R**8 < min(U)**k
 rs=set()
 if low:
  check(len(singles)*2>k and len(singles)>=2,'two controlled single marks missing')
  for i,j in combinations(singles,2):
   qi=next(q for q in Q if assigns[q]==i);qj=next(q for q in Q if assigns[q]==j)
   check(qi!=qj and F[i].get(qi,0)>0 and F[j].get(qj,0)>0,'zero witness or same mark')
   check(U[i]==V[i]*qi**F[i][qi] and U[j]==V[j]*qj**F[j][qj] and U[i]!=U[j],'false ratio')
   rs.add(V[i]!=V[j])
 return rs
real=synt=0;cases=set()
for n in range(8,162,2):
 Q=[p for p in range(3,n-1,2) if factor(p)=={p:1} and gcd(p,n)==1]
 if len(Q)<2:continue
 U=[n-p for p in Q]
 for rev in (False,True):
  cases|=test(U,Q,True,rev);real+=1
for n,Q in [(128,[3,5,7,11,13,23,29,41]),(2200,[3,13])]:
 for rev in (False,True):cases|=test([n-p for p in Q],Q,True,rev);real+=1
# Distinct composite values on a common prime alphabet; only the integer marking lemma is tested here.
for Q,U in [([3,5,7,11],[3**60*5,5**61*7,7**62*11,11**63*3]),([3,5],[3**9,5**7])]:
 for rev in (False,True):cases|=test(U,Q,True,rev);synt+=1
check(cases=={False,True},'both residual-ratio cases must be represented')
print('PASS exact marked-row controls:',real,'genuine centers/mark choices,',synt,'synthetic choices; equal and unequal residuals')
