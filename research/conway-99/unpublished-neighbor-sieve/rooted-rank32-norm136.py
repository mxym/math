import sympy as s
from math import isqrt, comb, factorial
from functools import lru_cache
from fractions import Fraction as F
from math import gcd,lcm
J=4
N=56*J
K=[u for u in range(N+1) if not 0<u<68 and u%8 not in (1,3)]
ik={u:i for i,u in enumerate(K)}
E4=[1]+[240*sum(d**3 for d in range(1,j+1) if not j%d) for j in range(1,J+1)];E6=[1]+[-504*sum(d**5 for d in range(1,j+1) if j%d==0) for j in range(1,J+1)]
def mul(a,b):return [sum(a[k]*b[j-k] for k in range(j+1)) for j in range(J+1)]
@lru_cache(None)
def pw(a,n):
 if not n:return [1]+[0]*J
 return mul(E4 if a==4 else E6,pw(a,n-1))
def null(w,cusp):
 m=[mul(pw(4,i),pw(6,(w-4*i)//6)) for i in range(w//4+1) if (w-4*i)%6==0]
 if cusp:m=[[u-v for u,v in zip(t,m[0])] for t in m[1:]]
 return s.Matrix(m).nullspace() if m else [s.eye(J+1)[:,i] for i in range(J+1)]
def cacheH(k,j):
 out=[{} for a in range(k+1)]; co=[]
 for a in range(k+1):
  b=k-a; coeff=[];den=1
  for i in range(k+1):
   for c in range(max(0,i-b),min(a,i)+1):
    d=i-c
    cc=comb(i,c)*factorial(2*a)//factorial(2*a-2*c)*factorial(2*b)//factorial(2*b-2*d)*14**c*28**d
    coeff.append((F((-2*j)**i*cc,den),2*a-2*c,2*b-2*d))
   den*=4*(i+1)*(16+2*k-2-i)
  common=lcm(*(t.denominator for t,_,_ in coeff))
  co.append((common,[(int(t*common),pi,qi) for t,pi,qi in coeff]))
 for p in range(isqrt(28*j)+1):
  for q in range(isqrt(56*j-2*p*p)+1):
   n=56*j-2*p*p-q*q; mu=(1+(p!=0))*(1+(q!=0))
   powsP=[p**i for i in range(2*k+1)];powsQ=[q**i for i in range(2*k+1)]
   for a,(common,coeff) in enumerate(co):
    ss=sum(cc*powsP[pi]*powsQ[qi] for cc,pi,qi in coeff)
    out[a][n]=out[a].get(n,0)+mu*F(ss,common)
 return out
rows=[]
for k in range(10):
 nr=null(16+2*k,k>0)
 nr=[v for v in nr if any(v[j] for j in range(1,J+1))]
 if not nr:continue
 FJ=[cacheH(k,j) for j in range(J+1)]
 for c in nr:
  for a in range(k+1):
   tt=[F(0)]*len(K)
   for j in range(J+1):
    if not c[j]:continue
    for n,v in FJ[j][a].items():
     if n in ik:tt[ik[n]]+=F(c[j])*v
   dd=lcm(*(v.denominator for v in tt))
   r=[int(v*dd) for v in tt];g=gcd(*r)
   if g:rows.append([v//g for v in r])

from sympy.polys.matrices import DomainMatrix
def rank(mat):
 return DomainMatrix.from_Matrix(s.Matrix(mat)).rank()
target=[(1 if n==68 else -30 if n==0 else 0) for n in K]
assert len(K)==120 and len(rows)==126
rr=rank(rows)
assert rr==102 and rank(rows+[target])==rr
print("PASS: rank 102 on 120 columns; W68=30 W0 under the gap")
