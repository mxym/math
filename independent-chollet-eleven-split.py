#!/usr/bin/env python3
"""Independent exact arithmetic audit of the Chollet order-eleven split.
Only the author's 15 rational schedule knots are copied from the input.
Run ordinary Python. This audit is not an alternative proof of the analytic
lemmas. It uses a linear s/E grid on the small side and unnormalized
factorial monomials with matching-expanded Sylvester determinants on the large side.
"""
if not __debug__: raise RuntimeError('run without -O')
from fractions import Fraction as R
from math import comb as C, factorial as f,isqrt
def root(x):
 x=R(x);D=10**10;v=isqrt(x.numerator*D*D//x.denominator)
 return R(v+(v*v*x.denominator<x.numerator*D*D),D)
def loglo(x):
 t=(x-1)/(x+1)
 return sum(2*t**(2*j+1)/(2*j+1)for j in range(17))
def table(n):
 d=[0]
 for k in range(1,n):
  dd={}
  for j,v in enumerate(d):
   dd[j]=max(dd.get(j,-1),v);jj=j+k;dd[jj]=max(dd.get(jj,-1),v+4*j+k+k*k)
  d=[dd[j]for j in range(C(k+1,2)+1)]
 return d
def der(m):return sum((-1)**k*C(m,k)*f(m-k)for k in range(m+1))
def cert(n,rr,parts):
 E=rr*rr;M=C(n,2);H=table(n);rad=root(R(n-1,n));rho=[0,0,1,root(R((n-2)**2,n*(n-1)))]+[rad**(k-2)for k in range(4,n+1)]
 P=[R(1),R(0)]
 for m in range(2,n+1):P.append(sum(rho[j]*P[m-j]for j in range(2,m+1))/m)
 def coeff(m,v,k):
  if v>m:return 0
  return R(k*C(n-v,m-v),C(m,3))*sum((-1)**i*C(m-v,i)*f(m-3-i)for i in range(m-v+1))
 prim={}
 for m in range(2,n+1):
  p=R(der(m-2),der(m));q=R(2,m-1)-2*p
  prim[m]=[C(n,m)*der(m),p/M,q/((n-2)*M),(1-p-q)/(3*C(n,4)),[coeff(m,v,k)for v,k in ((6,8),(5,4),(4,2),(3,2),(4,2))]if m>=3 else []]
 bl=[]
 for k in parts:
  n2,n3,n4=(R(C(k,i),C(n,i)) for i in (2,3,4));ss=C(k,2)*E
  aa=R(2,3) if k==4 else 1-2*rr/3;V=6*E+8*rr**3+9*rr**4 if k==4 else 3*E+2*rr**3
  bl.append((n2,n3,n4,ss,aa,loglo(1+aa*ss)/ss,loglo((1+V)/(1+aa*ss))/(V-aa*ss),aa*aa/(2*(1+aa*ss)**2)))
 def cell(j,l,u):
  # Work with x=s/E, not y=sqrt(s/E). All estimates below are divided by x.
  s2lo,s2hi=E**2*l,E**2*u;Qlo,Qhi=s2lo/M,E*E;Rlo=4*s2lo/n
  slope=H[j+1]-H[j];inter=H[j]-j*slope
  Rhi=E**2*(slope+(inter/(l if inter>0 else u)if inter else 0))
  u3=(-2*E+4*s2lo/n)/3
  u4=max(s2lo/2-3*Rhi/4+Qlo,s2lo/2-(R(3*(n-1),2)-1)*E**2)
  W=R(0)
  for i,k,o,S,a,L,J,K in bl:
   e=i*E;e2=o*s2hi+(k-o)*Rhi+(i-2*k+o)*Qhi
   W+=L*e+J*max(0,e+k*u3+o*u4-a*e)+K*max(0,S*e-e2)
  A=sum((2*W)**p*l**(p-1)/f(p)for p in range(1,18));B=R(0)
  for m,(N,a,b,c,ws)in prim.items():
   # Each increment bounds the same normalized U_m.
   h=a-b+c/2;g=(b-c)/2
   opts=[R(N,M)*E**m,P[m]*(root(R(2))*E)**m*root(u)**(m-2),N*E**(m-2)*(c*s2hi/2+g*(Rhi if g>=0 else Rlo)+h*(Qhi if h>=0 else Qlo))]
   if ws:
    j0,j1,j2,j3,j4=ws
    W1=E*u*min((n-2)*E**2,Rhi/2-Qlo)
    W2=min((n-1)**2*E**3,rad*root(2*u)*E*Rhi/2)
    W3=rho[3]*(root(R(2))*E)**3*root(u)/6
    W4=E*( (1-R(4,n))*s2hi+E**2)
    for b0 in (j0,j1,j2,j3):
     if b0>=j0:
      opts.append(E**(m-3)*(b0*E**3*u*u/6+sum(max(0,jj-b0)*ww for jj,ww in ((j1,W1),(j2,W2),(j3,W3)))+j4*W4))
   B+=min(opts)
  return A-B
 # Repartition each unit x-interval independently on a fixed four-cell grid.
 g=[]
 for j in range(M):
  for k in range(4):
   d=cell(j,R(j)+R(k,4),R(j)+R(k+1,4));assert d>0,(j,k,float(d));g.append(d)
 print('independent x=s/E grid',n,len(g),'gap >=',min(g)*10**6//1,'ppm',flush=True)
cert(7,R(1,5),(4,3));cert(9,R(8,25),(4,4));cert(11,R(21,50),(4,4,3))

from fractions import Fraction as F
from math import factorial as fact
from itertools import combinations
SCHEDULE=tuple(tuple(F(str(x)) for x in row) for row in (
    ("0.417","1.48133","1.14730","1.170487"),
    ("0.427","1.48627","1.14456","1.174417"),
    ("0.447","1.49619","1.13919","1.182590"),
    ("0.477","1.51138","1.13124","1.195609"),
    ("0.507","1.52572","1.12400","1.210275"),
    ("0.557","1.54394","1.11480","1.244647"),
    ("0.607","1.54975","1.10900","1.284309"),
    ("0.657","1.55322","1.08219","1.338245"),
    ("0.707","1.55674","1.06407","1.388635"),
    ("0.757","1.55941","1.04920","1.443152"),
    ("0.807","1.56011","1.03000","1.515470"),
    ("0.857","1.56184","1.01969","1.577454"),
    ("0.907","1.56216","1.00967","1.651524"),
    ("0.957","1.56242","1.00332","1.721998"),
    ("1","1.56120","1.00021","1.779121"),
))
def dmatch(diag,edge):
 # Sum over path matchings: fixed points contribute diagonal entries,
 # each matching edge contributes the negative square of the subdiagonal.
 n=len(diag);out=F(0)
 for k in range(n//2+1):
  for sub in combinations(range(n-1),k):
   if any(b==a+1 for a,b in zip(sub,sub[1:])):continue
   used=set(sub)|{j+1 for j in sub};p=(-1)**k
   for i in sub:p*=edge[i]**2
   for i in range(n):
    if i not in used:p*=diag[i]
   out+=p
 return out
def mean(r,t,u):
 A=(1+r)**2*(u*u-1);B=(1-r)**2*(t*t-1)
 return (A*t*t+B*u*u)/(A+B)
def check(r,R,t,T,u,U,m,M):
 c,s=(1+r)/2,(1-R)/2;C,S=(1+R)/2,(1-r)/2
 v,z=(1+R**2)/2,(1-r**2)/2
 w=mean(r,t,u);y=t*u
 assert t>U>1 and m>0
 nd=0
 for k in range(10):
  for start in (0,1):
   N=[];P=[];Ne=[];Pe=[]
   for a in range(start,k+1,2):
    b=k-a
    N.append(c*c*fact(a+2)*fact(b)+s*s*fact(a)*fact(b+2)-M*T**a*U**b*fact(a)*fact(b))
    P.append(m*m*w**a*y**b*fact(a)*fact(b)-v*v*fact(a+2)*fact(b)-z*z*fact(a)*fact(b+2))
    if a>start:Ne.append(C*S*fact(a)*fact(b+2));Pe.append(v*z*fact(a)*fact(b+2))
    assert dmatch(N,Ne)>0 and dmatch(P,Pe)>0, (r,R,k,a)
    nd+=2
 return nd
num=0;sub=20
for l,v in zip(SCHEDULE,SCHEDULE[1:]):
 ar=[tuple((x*(sub-i)+y*i)/sub for x,y in zip(l,v))for i in range(sub+1)]
 for p,q in zip(ar,ar[1:]):
  r,t,u,m=p;R,T,U,M=q
  num+=check(r,R,min(t,T),max(t,T),min(u,U),max(u,U),min(m,M),max(m,M))
assert ar[-1][0]==1 and SCHEDULE[0][0]==F(417,1000)
print("factorial-basis independent Sylvester matching determinants:",num,"in",sub*(len(SCHEDULE)-1),"closed r-cells")
