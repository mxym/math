#!/usr/bin/env python3
"""Exact arithmetic and geometric regression gates for the explicit modulus.
These finite checks corroborate, not replace, the written proof.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
from random import Random
import json,sys
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]/"results"
ROOT.mkdir(exist_ok=True)
rng=Random(2026100707)
def need(x,s):
 if not x:raise RuntimeError(s)
def det(rows):
 a=[list(map(F,row)) for row in rows];n=len(a);ans=F(1)
 for i in range(n):
  k=next((j for j in range(i,n) if a[j][i]),None)
  if k is None:return F(0)
  if k!=i:a[k],a[i]=a[i],a[k];ans=-ans
  q=a[i][i];ans*=q
  for j in range(i+1,n):
   f=a[j][i]/q
   for h in range(i+1,n):a[j][h]-=f*a[i][h]
 return ans

def affine(base,y):return det([tuple(x-z for x,z in zip(v,y)) for v in base])
def pow10(k):return F(10**k) if k>=0 else F(1,10**(-k))
def log10_bounds(x):
 k=len(str(x.numerator))-len(str(x.denominator))
 if x<pow10(k):k-=1
 need(pow10(k)<=x<pow10(k+1),'exact decimal order')
 return [k,k+1]

def constants(d):
 R=d*(d+1);b=F(1,4*(d*R)**d);M=2/b;L=d*2**d;Z=M*(2*d+3);C=4*d*d*R*(M+1)
 p=(d+1)**2+1;dp=d*p;chi=b**d*(b**d/(12*d*L))**(d*(d+1))
 eta0=min(F(1,2*(d+1)),b/(4*d),1/Z,1/(Z*(8*M*d*C)**d));e0=chi*eta0**p/(2*(d+1))
 Apower=(4*M*d*C)**dp*Z**p*F(2*(d+1),chi)
 Gpower=max(Apower,F((R-1)**dp,e0))
 need(Apower*e0<=F(1,2)**dp,'local containment <= 1/2')
 need(C**d >= (2*d*R*(M+1))**d*d*2**(d-1),'cap constant enlargement')
 for eta in (eta0,eta0/2,eta0/100):
  r=eta*b**d/(4*L);tau=eta*(r/(3*d))**d;gamma=eta*b**d
  need(L*r==gamma/4,'robust determinant quarter margin')
  need(tau**(d+1)*gamma==chi*eta**p,'threshold exponent and coefficient')
  need(r<=eta<=1 and 2*b-eta-r>=b,'retained directional mass')
  need(2*d*eta<=b/2,'polar simplex inradius')
  need(Z*eta<=1,'mixed-volume linear bound')
  need(C**d*Z*eta <= F(1,8*M*d)**d,'small Hausdorff threshold')
 return {'dimension':d,'exponent':f'1/{dp}','R':R,'b':str(b),'M':str(M),'L':L,'Z':str(Z),'C':str(C),'p':p,'chi_log10_interval':log10_bounds(chi),'eta0_log10_interval':log10_bounds(eta0),'defect_threshold_log10_interval':log10_bounds(e0),'A_power_log10_interval':log10_bounds(Apower),'G_power_log10_interval':log10_bounds(Gpower),'power_for_constants':dp,'all_exact_checks':True}

def determinant_lipschitz():
 count=0
 for d in range(2,6):
  L=d*2**d
  for _ in range(100):
   pts=[tuple(F(rng.randrange(-10,11),20*d) for j in range(d)) for i in range(d+1)]
   r=F(1,rng.randrange(20,100));new=[tuple(a+F(rng.randrange(-10,11),10*d)*r for a in x) for x in pts]
   need(all(sum(a*a for a in x)<=1 for x in pts+new),'unit-ball test data')
   need(all(sum((a-b)**2 for a,b in zip(x,y))<=r*r for x,y in zip(pts,new)),'test perturbation norm')
   need(abs(affine(pts[:-1],pts[-1])-affine(new[:-1],new[-1]))<=L*r,'Lipschitz determinant')
   count+=1
 return count

def barycentric_matrices():
 count=0
 for n in range(3,8):
  for _ in range(80):
   # Columns = a near-identity probability kernel with a random permutation.
   rows=list(range(n));rng.shuffle(rows);cols=[]
   for j in range(n):
    small=[rng.randrange(1,10) for k in range(n)];total=sum(small);eps=F(rng.randrange(1,5),100*n)
    col=[eps*F(w,total) for w in small];col[rows[j]]+=1-eps;cols.append(col)
   q=abs(det(cols));delta=1-q
   if delta>F(1,8):continue
   dominant=[max(range(n),key=lambda i:col[i]) for col in cols]
   need(len(set(dominant))==n,'dominant permutation')
   for col,i in zip(cols,dominant):need(col[i]>=1-2*delta,'dominant coefficient bound')
   count+=1
 return count

def nonatomic_witnesses():
 out=[]
 for d in (2,3):
  vertices=[(-F(1,4),)*d]+[tuple(F(int(i==j),4) for i in range(d)) for j in range(d)]
  z=(F(0),)*d;base=[z]+vertices[2:];vp,vq=vertices[:2]
  dp=affine(base,vp);dq=affine(base,vq)
  need(dp*dq<0,'centered simplex interior sign witness')
  V=abs(affine(vertices[1:],vertices[0]));eta=F(1,2*(d+1));gamma=eta*V;L=d*2**d;r=gamma/(4*L)
  h=r/d;centers=vertices+[z];weight=F(1,d+2)
  corners={x:[tuple(a+h*s for a,s in zip(x,signs)) for signs in product((-1,1),repeat=d)] for x in centers}
  need(all(any(abs(a-b)>2*h for a,b in zip(x,y)) for i,x in enumerate(centers) for y in centers[i+1:]),'witness boxes disjoint')
  for cs in corners.values():need(all(sum(a*a for a in x)<=1 for x in cs),'box within unit ball')
  checks=0;smallest=None
  for last,sgn in [(vp,1 if dp>0 else -1),(vq,1 if dq>0 else -1)]:
   for actual in product(*(corners[x] for x in base+[last])):
    value=sgn*affine(actual[:-1],actual[-1]);need(value>=gamma/2,'nonatomic box sign margin')
    smallest=value if smallest is None else min(smallest,value);checks+=1
  # Separate affine dependence gives extrema at box corners, so the checked
  # margins hold throughout each product box. Uniform box laws have no atoms.
  lower=weight**(d+1)*gamma
  out.append({'dimension':d,'centers':[list(map(str,x)) for x in centers],'mass_each':str(weight),'box_half_side':str(h),'corner_sign_tests':checks,'smallest_signed_corner_determinant':str(smallest),'guaranteed_cancellation_defect_lower_bound':str(lower),'nonatomic_law':'Equal mixture of normalized uniform measures on the disjoint symmetric boxes; center zero.'})
 return out

if __name__=='__main__':
 result={'constants':[constants(d) for d in range(2,9)],'determinant_perturbation_cases':determinant_lipschitz(),'stochastic_barycentric_cases':barycentric_matrices(),'nonatomic_box_witnesses':nonatomic_witnesses(),'scope':'Finite exact regressions; the general theorem is the complete written proof.'}
 (ROOT/'exact_gate_results.json').write_text(json.dumps(result,indent=2)+'\n')
 print('PASS:',len(result['constants']),'dimensions of exact constants;',result['determinant_perturbation_cases'],'determinant perturbations;',result['stochastic_barycentric_cases'],'barycentric matrices;',sum(x['corner_sign_tests'] for x in result['nonatomic_box_witnesses']),'nonatomic corner-sign tests.')
