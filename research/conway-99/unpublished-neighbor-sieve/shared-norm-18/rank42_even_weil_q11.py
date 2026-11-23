"""Exact auxiliary-theta coefficient and Fourier-entry check (requires SymPy)."""

from fractions import Fraction as Q
from collections import Counter
from functools import cache
from itertools import product
from math import isqrt
import sympy as sm
def orbit(a,b):
 x=[(a,b),((-b)%7,a),((-a)%7,(-b)%7),(b,(-a)%7)]
 j=min(range(4),key=lambda i:x[i])
 return (*x[j],(-1)**j)
def coeff_slots(J):
 V={(c,d)for a,b in product(range(7),repeat=2)if a or b for c,d,z in [orbit(a,b)]}
 return [(j,a,b)for j in range(J+1)for a,b in sorted(V)if (2*j-a*a-b*b)%7==0]
def aux_theta_vector(h,p,J):
 hs=2*h[0]**2+2*h[0]*h[1]+4*h[1]**2+2*h[2]**2+2*h[2]*h[3]+4*h[3]**2
 ds=[Q(1)]
 for j in range(p//2):
  m=p-2*j
  ds.append(ds[-1]*Q(-m*(m-1),2*(j+1)*(4+2*p-2*j-4)))
 H=Counter();R=[isqrt(2*J*t//7)for t in (2,4,2,4)]
 for u in product(*(range(-r,r+1)for r in R)):
  w,x,y,z=u;j=2*w*w-w*x+x*x+2*y*y-y*z+z*z
  if j>J:continue
  a=5*(w+5*x)%7;b=5*(y+5*z)%7
  if not (a or b):continue
  a,b,s=orbit(a,b)
  ip=sum(x*v for x,v in zip(u,h))
  f=sum(c*ip**(p-2*k)*Q(2*j*hs,7)**k for k,c in enumerate(ds))
  H[j,a,b]+=f*s/4
 return H
@cache
def eis(k,N):
 if k==2:C=-24
 elif k==4:C=240
 elif k==6:C=-504
 else:raise ValueError(k)
 return [1]+[C*sum(d**(k-1)for d in range(1,n+1)if n%d==0)for n in range(1,N+1)]
def mul_vec(F,ss,E):
 return {k:sum(e*F.get((k[0]-7*i,*k[1:]),0)for i,e in enumerate(E)if 7*i<=k[0])for k in ss}
def derive(F,ss,k,J):
 G=mul_vec(F,ss,eis(2,J//7))
 return {z:Q(z[0],7)*F.get(z,0)-Q(k,12)*G[z]for z in ss}

def candidate_basis(J,total,limit):
 ss=coeff_slots(J);B={}
 D=[(0,0,0,1),(0,0,1,0),(0,1,0,1),(0,1,0,-1),(1,0,0,1),(1,1,1,1),
    (0,1,1,1),(1,2,3,1),(2,-1,1,0),(0,2,3,1),(1,-1,2,-1),(2,2,1,1)]
 for p in range(0,total-1,2):
  for h in D:
   f=aux_theta_vector(h,p,J)
   w=2+p
   while w<=total:
    for a in range((total-w)//4+1):
     q=total-w-4*a
     if q%6:continue
     g=f
     for _ in range(a):g=mul_vec(g,ss,eis(4,J//7))
     for _ in range(q//6):g=mul_vec(g,ss,eis(6,J//7))
     v=[Q(g.get(k,0))for k in ss]
     for i,z in sorted(B.items()):
      c=v[i]
      if c:v=[x-c*y for x,y in zip(v,z)]
     if any(v):
      i=next(i for i,x in enumerate(v)if x);B[i]=[x/v[i]for x in v]
     if len(B)==limit:
      print("explicit weight",total,"full rank at p,h",p,h,"through degree",J)
      return ss,list(B.values())
    f=derive(f,ss,w,J);w+=2
 return ss,list(B.values())
def vector_basis(J):
 ss,B=candidate_basis(J,22,20)
 if len(B)==20:return ss,B
 print("direct generated weight22",len(B))
 ss2,C=candidate_basis(J+7,34,32)
 print("direct generated weight34",len(C))
 F=sm.Matrix(C).T
 N=F[[i for i,(j,a,b)in enumerate(ss2)if j<7],:].to_DM().nullspace().to_Matrix().T
 H=F*N;D=[]
 d=[1,-24,252,-1472,4830]
 for z in H.T.tolist():
  f=dict(zip(ss2,z));g={}
  for (j,a,b)in ss:
   g[j,a,b]=f[j+7,a,b]-sum(d[l]*g.get((j-7*l,a,b),0)for l in range(1,j//7+1))
  D.append([g[k]for k in ss])
 E,piv=sm.Matrix([*B,*D]).to_DM().rref()
 print("after cusp division rank",len(piv))
 assert len(piv)==20
 return ss,E.to_Matrix().tolist()[:len(piv)]

def check_irreducibility():
    representatives = [
      next((a,b) for a,b in product(range(7), repeat=2) if (a*a+b*b)%7==r)
      for r in range(1,7)]
    for (x,y),(u,v) in product(representatives, repeat=2):
        R,I=[0]*7,[0]*7
        for k in range(8):
            r=(x*u+y*v)%7
            R[r]+=(1,0,-1,0)[k%4]
            I[r]+=(0,1,0,-1)[k%4]
            u,v=(2*(u-v))%7,(2*(u+v))%7
        assert len(set(zip(R,I)))>1
    print("all 36 order-four finite Fourier entries nonzero")

def main():
 check_irreducibility()
 J=16
 S,B=vector_basis(J)
 F=sm.Matrix(B).T
 for cond,expected in [(lambda n:n<11,2),(lambda n:n<11 or n==12,0)]:
  Z=F[[i for i,k in enumerate(S)if cond(k[0])],:]
  d=len(B)-Z.to_DM().rank()
  assert d==expected
  print("filtered dimension",d)
if __name__ == "__main__":
 main()
