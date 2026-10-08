from fractions import Fraction as Q
from itertools import combinations
from math import factorial
from pathlib import Path
import json
R=Path(__file__).resolve().parent

def det(rows):
 a=[list(r) for r in rows];n=len(a);v=Q(1)
 for i in range(n):
  p=next((j for j in range(i,n) if a[j][i]),None)
  if p is None:return Q(0)
  if p!=i:a[i],a[p]=a[p],a[i];v=-v
  z=a[i][i];v*=z
  for k in range(i+1,n):
   w=a[k][i]/z
   for j in range(i+1,n):a[k][j]-=w*a[i][j]
 return v

def sum_minors(rows,n):return sum(abs(det([rows[i] for i in iset])) for iset in combinations(range(len(rows)),n))
results=[]
for d in range(2,7):
 for t in [Q(1,10),Q(1,2),Q(9,10)]:
  c=Q(1,factorial(d-1));q=t**(d-1);s=t**d;r=1-q
  u=[[c]*d,[-c*q]*d]+[[-c*r*Q(i==j) for j in range(d)] for i in range(d)]
  ell=[[c]+u[0],[-c*s]+u[1]]+[[Q(0)]+row for row in u[2:]]
  H=sum_minors(u,d);L=sum_minors(ell,d+1)
  Hf=c**d*r**(d-1)*(d+1+(d-1)*q)
  Lf=c**(d+1)*r**(d-1)*(1+(d-1)*q-(d-1)*s-q*s)
  assert H==Hf and L==Lf
  vol=(1-s)/factorial(d);e=L/(d*vol*H)-Q(1,d+1)
  ef=q*(d*(d-1)-(d+1)*(d-2)*t-2*s)/((d+1)*(1-s)*(d+1+(d-1)*q))
  assert e==ef and e>0
  vertices=[[Q(i==j) for j in range(d)] for i in range(d)]
  vertices+= [[t*Q(i==j) for j in range(d)] for i in range(d)]
  maxdet=max(abs(det([[Q(1)]+vertices[i] for i in iset])) for iset in combinations(range(2*d),d+1))
  assert maxdet==1-t
  wrong=[list(row) for row in ell];wrong[1][0]=-wrong[1][0]
  assert sum_minors(wrong,d+1)!=L
  assert L/(d*vol*H)/(d+1)-Q(1,d+1)!=e
  j=1;point=vertices[d+j];beta0=(1-sum(point))/(1-t);betai=point[0]-t*beta0
  assert betai==-t
  results.append({'d':d,'t':str(t),'H':str(H),'L':str(L),'defect':str(e),'maximum_lifted_vertex_determinant':str(maxdet),'centroid_excess':str((d+1)*t),'wrong_bottom_support_sign_rejected':True,'wrong_ordered_factorial_rejected':True})
(R/'checks/exact-rational-controls.json').write_text(json.dumps({'scope':'Finite rational corroboration only; Lean proof establishes arbitrary dimension.','cases':results,'count':len(results)},indent=2))
print('PASS exact rational geometry/determinant/defect/max-simplex/centroid controls',len(results))
