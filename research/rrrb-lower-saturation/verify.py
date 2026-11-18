"""Exact arithmetic certificate for the lower saturation threshold; Python standard library."""
from fractions import Fraction as Q
from math import comb

def det(a):
 a=[list(map(Q,row)) for row in a]; n=len(a); value=Q(1)
 for col in range(n):
  j=next((j for j in range(col,n) if a[j][col]),None)
  if j is None:return Q(0)
  if j!=col:a[j],a[col]=a[col],a[j];value=-value
  d=a[col][col];value*=d
  for j in range(col+1,n):
   z=a[j][col]/d
   if z:a[j]=[v-z*w for v,w in zip(a[j],a[col])]
 return value

def J(p):return 65536*p**4-86528*p**3+39133*p**2-5378*p-139
def pols(p):
 x=4*p-1; a=2*p-4*p*p
 # descending coefficients in r; D=r^4,...,1
 K=[16,-12*x,x*x-8*a,a*x]
 D=[-3,12*p-5,-18*p*p+14*p-1,p*(3*p-1)*(4*p-3),p*p*(1-p)*(3*p-1)]
 return K,D
for p in map(Q,range(-12,13)):
 k,d=pols(p)
 # independent check expanded D and K at enough r's (degree at most 4).
 for r in map(Q,range(-2,3)):
  val=lambda poly: sum(v*r**i for i,v in enumerate(reversed(poly)))
  P=p*(1-p);x=4*p-1;C=2*p-4*p*p+x*r-4*r*r
  assert val(k)==C*(x-8*r)-16*r**3
  assert val(d)==(P+r*r)**2-(p-r)*(1-p+r)*C
 mat=[[0]*i+k+[0]*(3-i) for i in range(4)]+[[0]*i+d+[0]*(2-i) for i in range(3)]
 assert det(mat)==p*p*J(p)
print('25 exact Sylvester determinants: resultant identity through degree 24 PASS')

def transformed(lo,hi):
 coeff=[-139,-5378,39133,-86528,65536];res=[Q(0)]*5
 for k,f in enumerate(coeff):
  for i in range(k+1):
   for j in range(5-k):
    res[i+j]+=f*comb(k,i)*lo**(k-i)*hi**i*comb(4-k,j)
 return res
c=transformed(Q(0),Q(1,4));assert all(v<0 for v in c)
c=transformed(Q(1,4),Q(1,3))
assert c==[Q(-2139,16),Q(-8713,24),Q(-42515,144),Q(-1303,27),Q(1684,81)]
assert J(Q(32053506,10**8))<0<J(Q(32053508,10**8))
p=Q(1,4);r=0;assert pols(p)[1][-1]==Q(-3,256)
for r in map(Q,range(-2,3)):
 p=Q(1,3); D=sum(z*r**i for i,z in enumerate(reversed(pols(p)[1])))
 assert D==r*r*(5-3*r-9*r*r)/3
print('Descartes signs, rational isolating interval and both endpoint tests PASS')
