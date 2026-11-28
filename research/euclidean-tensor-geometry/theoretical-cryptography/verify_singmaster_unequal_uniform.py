#!/usr/bin/env python3
"""Exact uniform Runge certificate for (a,b)=(d,2d),(2d,d), d>=2.
Requires SymPy. Option --determinants replays the independent full-rank invariant.
"""
from fractions import Fraction as Q
from math import factorial
from sympy import symbols, Poly, QQ, Matrix, Rational, interpolate, factor
from sys import argv

zero=(Q(0),)*3
one=(Q(1),Q(0),Q(0))
tau=(Q(0),Q(1),Q(0))
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def scale(x,s):return tuple(a*s for a in x)
def minus(x,y):return add(x,scale(y,-1))

def make(p,q):
 # G=t^3+g2*t^2+g1*t-1.
 g=(Q(-1),Q(1 if p==2 else 0),Q(p))
 t=symbols('t')
 G=Poly(t**3+p*t**2+(1 if p==2 else 0)*t-1,t,domain=QQ)
 def mul(x,y):
  a=[Q(0)]*5
  for i,h in enumerate(x):
   for j,k in enumerate(y):a[i+j]+=h*k
  for i in [4,3]:
   for j,n in enumerate(g):a[i-3+j]-=a[i]*n
  return tuple(a[:3])
 def inv(x):
  X=Poly(sum(a*t**i for i,a in enumerate(x)),t,domain=QQ)
  U=X.invert(G);return tuple(Q(U.nth(i)) for i in range(3))
 def sfrac(series, N):
  x=inv(series[0])
  A=[x]
  for n in range(1,N+1):
   v=zero
   for i in range(1,min(n+1,len(series))):
    v=add(v,mul(series[i],A[n-i]))
   A.append(scale(mul(x,v),-1))
  return A
 def smul(A,B,N):
  C=[zero]*(N+1)
  for i,x in enumerate(A[:N+1]):
   for j,y in enumerate(B[:N+1-i]):C[i+j]=add(C[i+j],mul(x,y))
  return C
 def spow(A,h,N):
  C=[one]+[zero]*N
  for i in range(h):C=smul(C,A,N)
  return C
 base1=[one,scale(one,Q(1,2))]
 Ader=G.diff().invert(G)
 ainv=tuple(Q(Ader.nth(i)) for i in range(3))
 def moment(k,j,D):
  x=k*k*D
  if j==1:return Q(k*(x-1),12)
  if j==2:return Q(k*(x-1)*(3*x-7),240)
  return Q(k*(x-1)*(3*x*x-18*x+31),1344)
 def B(T,N):
  # A(T)=prod normalized monomials (1+T)^p*T^q.
  B=T[:];B[0]=add(one,B[0])
  return smul(spow(B,p,N),spow(T,q,N),N)
 def RHS(T,D,N):
  B=T[:];B[0]=add(one,B[0])
  inverses=[sfrac(C,max(N-2,0)) for C in (B,T,base1)]
  L=[zero]*(N+1)
  for h in range(1,N//2+1):
   f,g,k=[spow(A,2*h,N-2*h) for A in inverses]
   for j in range(N-2*h+1):
    v=add(scale(f[j],moment(p,h,D)),scale(g[j],moment(q,h,D)))
    v=minus(v,scale(k[j],moment(3,h,D)))
    L[j+2*h]=add(L[j+2*h],scale(v,Q(1,2*h)))
  E=[one]+[zero]*N
  for i in range(1,N//2+1):
   E=[add(x,scale(y,Q(1,factorial(i)))) for x,y in zip(E,spow(L,i,N))]
  return smul(spow(base1,3,N),E,N)
 def expand(D,N=6):
  T=[tau]
  for j in range(1,N+1):
   T.append(mul(ainv,minus(RHS(T,D,j)[j],B(T,j)[j])))
  assert all(x==y for x,y in zip(RHS(T,D,N),B(T,N)))
  return T
 def matrix(D, P=False):
  T=expand(D); TT=[spow(T,j,6) for j in range(3)]
  BB=B(T,6);BB[0]=minus(BB[0],one)
  M=[];Dpolys=[]
  for a,b in [(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]:
   C={a+b+3-i:v for i,v in enumerate(smul(BB,TT[b],6))}
   est=[]; V={}
   for j in range(a+b+3,-1,-1):
    v=C.get(j,zero)
    est.append(v[min(3,j+1):])
    for h,z in enumerate(v[:j+1]):
     if not z:continue
     V[j-h,h] = -z
     for k,w in enumerate(TT[h][:j+2]):
      C[j-k]=minus(C.get(j-k,zero),scale(w,z))
   if P:Dpolys.append((a,b,V))
   M.append(tuple(x for R in est for x in R)+C.get(-1,zero))
  assert all(len(r)==6 for r in M)
  return (Matrix(M).T,Dpolys) if P else Matrix(M).T
 return matrix

from math import lcm,ceil
from collections import defaultdict
D=symbols('D')
SELECT={(1,2):(0,1,2,3),(2,1):(0,2,3,4)}
BOX={(1,2):(Q(3,4),Q(19,25)),(2,1):(Q(23,50),Q(47,100))}

def fcase(p,q):
 M=make(p,q);J=SELECT[p,q]
 assert M(1)==Matrix.zeros(6,6)
 samples=[];levels=[];ell=[]
 for dval in range(2,8):
  A,records=M(dval,True)
  assert dval>=2
  T=A[:3,:]/(dval-1)
  cof=[(-1)**j*T[:,list(J[:j]+J[j+1:])].det() for j in range(4)]
  v=A[:,list(J)]*Matrix(cof)
  assert all(x==0 for x in v[:3])
  ell.append(list(v[3:]))
  w=defaultdict(Q)
  for j,co in zip(J,cof):
   a,b,start=records[j]
   H={(a+3,b):-1,(a,b+3):1,(a+1,b+2):p}
   if p==2:H[a+2,b+1]=1
   for origin in [start,H]:
    for key,value in origin.items():w[key]+=Q(co)*value
  assert all(i+j<=5 for i,j in w)
  samples.append(w);levels.append(dval)
 def fit(vals):
  return Poly(interpolate(list(zip(levels,vals)),D),D,domain=QQ)
 C={key:fit([x.get(key,0) for x in samples]) for key in set().union(*samples)}
 V=[fit([e[j] for e in ell]) for j in range(3)]
 assert max(c.degree() for c in C.values())<=4 and max(c.degree() for c in V)==5
 assert V[0].eval(1)==V[1].eval(1)==V[2].eval(1)==0
 lo,hi=BOX[p,q]
 G=lambda t0:(1+t0)**p*t0**q
 assert G(lo)<1<G(hi)
 V4=[v.shift(4) for v in V]
 low=[]
 for i in range(6):
  h=[Q(v.nth(i)) for v in V4]
  low.append(sum(min(z*lo**j,z*hi**j) for j,z in enumerate(h)))
 assert all(x>0 for x in low)
 den=32*lcm(*(z.q for c in C.values() for z in c.all_coeffs()))
 B=2*den*(1+sum(abs(Q(z)) for c in C.values() for z in c.all_coeffs()))
 K=den*sum(abs(Q(z)) for v in V for z in v.all_coeffs())
 delta=den*min(low[5]/32,low[0]/(8**5))
 maxW=1+ceil(max(2*1024,2*K,4*B*1024**7/delta))
 print('uniform',p,q,'den',den,'majorant',B,'lambdaMax',K,'delta',delta,'cutoff',maxW,flush=True)
 return C,V,den,maxW

# The determinant calculation is redundant for the fixed-cofactor bound; it
# additionally certifies that no polynomial of degree <= 5 vanishes on a
# positive branch of either family when d >= 2.
DET_ROWS={
 (1,2): (13915128861476020813824000000,
          [-117734593683482075,12734866608004690948,-231808532062890786728,869190295438308677764,-105687887512187069030,-343686140643234727700,-7230862920217363822352,1881137758566998659852,1847539071680326461049]),
 (2,1): (3607626001123412803584000000,
          [-31988553088107544903,428779702049959343284,-1884264812856071352360,2667744061296321794228,352295209003388969890,-830920500991351447428,-2713813890872058067696,-72769861328932361060,679698695894985324093]),
}
def determinant_check(p,q):
    den, coeff=DET_ROWS[p,q]
    A=Poly(sum(c*D**i for i,c in enumerate(coeff)),D,domain=QQ)
    assert min(A.shift(4).all_coeffs())>0
    target=(Poly(D-1,D,domain=QQ)**6)*A/den
    M=make(p,q)
    for k in range(15):
        assert M(k).det()==target.subs(D,k)
    print("six-dimensional residual determinant PASS",p,q,flush=True)

def main():
    for p,q in SELECT:
        C,V,den,cutoff=fcase(p,q)
        assert cutoff<10**29
        if "--determinants" in argv:
            determinant_check(p,q)
    print("PASS",flush=True)
if __name__=="__main__":main()
