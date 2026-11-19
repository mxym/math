"""Finite, exact rational checks of the moving-odds parametrization and parity factors.
These checks do not establish the limit theorem."""
from itertools import product
from fractions import Fraction as F
from math import prod,comb,factorial

def require(z,s):
 if not z:raise ArithmeticError(s)
def det(A):
 A=[r[:] for r in A]; d=F(1)
 for j in range(len(A)):
  k=next((k for k in range(j,len(A)) if A[k][j]),None)
  if k is None:return F(0)
  if k!=j:A[j],A[k]=A[k],A[j];d=-d
  v=A[j][j];d*=v
  for i in range(j+1,len(A)):
   coeff=A[i][j]/v
   for l in range(j,len(A)):A[i][l]-=coeff*A[j][l]
 return d

def mass(q,bits):
 return prod((v if bit else 1-v) for v,bit in zip(q,bits))
count=0;atoms=0
for m in range(2,10):
 q0=[F(2*i+1,2*m) for i in range(m)]
 for q in [q0,q0[::-1], [F(1,2)]*m]:
  require(sum(q)==F(m,2),'slice')
  for r in map(F,[1,F(5,4),F(7,4),3]):
   k=[(1-v)/r+v*r for v in q]
   u=[v*r/t for v,t in zip(q,k)]
   M=[]
   for i,(v,t,ui) in enumerate(zip(q,k,u)):
    M.append([(F(int(i==j)-int(i==m-1))/t**2) for j in range(m-1)]+[2*ui*(1-ui)])
   J=abs(det(M)); require(J==2*sum(v*(1-v) for v in q)/prod(k)**2,'full Jacobian')
   B=bo=F(0)
   for bits in product(range(2),repeat=m):
    S=sum(bits); orig=mass(u,bits);tilt=mass(q,bits)
    require(orig==tilt*r**(2*S-m)/prod(k),'pointwise inner tilt')
    if 2*S<=m:
     j=m//2-S
     B+=tilt*r**(-(m%2+2*j));bo+=orig
    atoms+=1
   require(bo==B/prod(k),'strict tie, parity normalizer')
   if r>1:require(sum(u)>F(m,2) and J>0,'correct half cube')
   count+=1
print('PASS:',count,'exact full Jacobians;',atoms,'exact likelihoods; loss/tie masses across both parities.')
# Exact central slice volumes from the density formula for a sum of m uniforms.
for m,ans in [(2,F(1)),(3,F(3,4)),(4,F(2,3)),(5,F(115,192)),(6,F(11,20))]:
 f=sum((-1)**j*comb(m,j)*(F(m,2)-j)**(m-1) for j in range(m//2+1))/factorial(m-1)
 require(f==ans,('slice normalization',m,f,ans))
print('PASS: exact central slice measures in first m-1 coordinates, dimensions m=2..6.')
