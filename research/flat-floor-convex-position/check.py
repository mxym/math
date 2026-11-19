"""Optional finite rational checks. The general results are analytic."""
from fractions import Fraction as F
from math import factorial, comb
def add(a,b):
 out=[0]*max(len(a),len(b))
 for i,z in enumerate(a):out[i]+=z
 for i,z in enumerate(b):out[i]+=z
 return out
def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
def scale(a,k):return [x*k for x in a]
def integ(a):return [0]+[F(x,i+1) for i,x in enumerate(a)]
def val(a,x):
 r=0
 for y in a[::-1]:r=r*x+y
 return r
def segment(a,l,r):
 b=integ(a);return val(b,r)-val(b,l)
def same(x,y,loc):
 if x!=y:raise ValueError(f"exact check failed at {loc}: {x} vs {y}")
def triangle(j):return F(2**j,factorial(j)*factorial(j+1))
def bn(n,k):
 return [0]*k+[(-1)**i*comb(n,k)*comb(n-k,i) for i in range(n-k+1)]
def upper():
 for n in range(2,33):
  m=n-1;p=[0]
  for k in range(m+1):p=add(p,scale(bn(m,k),F(1,2**m)*triangle(k)*triangle(m-k)))
  q=F(comb(2*n,n),factorial(n)*factorial(n+1));same(segment(p,F(0),F(1)),q,n)
  D=2*segment(mul([0,4],p),F(0),F(1,2))-q
  if n==2:same(D,0,'two sample first variation')
  elif D<=0:raise ValueError(f'nonpositive first variation {n}')
  if n==3:same(3*D,F(1,24),'three sample first variation')
 # Use explicit square splitting from UPPER.md, not a random estimate.
 t=F(1,2);g=[F(4,5),F(4,5)];gr=[F(8,5),-F(4,5)]
 a=add([1],scale(g,-F(1,2)))
 base=2*segment(mul(g,mul(a,a)),0,t)
 loss1=segment(mul(g,[0,0,F(16,75)]),0,t)
 loss2=segment(mul(gr,[F(8,75),F(-40,75),F(64,75)]),t,1)
 same((base,loss1,loss2),(F(37,150),F(11,1125),F(12,125)),'split cap')
 same(base-loss1-loss2,F(317,2250),'pentagon probability')
 print('Triangle split: n=2..32 exact; no truncation in all-n proof.')
 print('Pentagon 317/2250; square 5/36; excess 1/500.')

def lower_constants():
 for n in range(2,41):
  m=n-1
  # Integrals of each degree-m Bernstein basis polynomial equal 1/n.
  cn=sum(triangle(j)*triangle(m-j) for j in range(n))/2**m
  J=F(2**n*factorial(m)*factorial(n),factorial(2*n))
  same(cn*J,triangle(n),("triangle calibration",n))
 print("Highest-point split benchmark calibrates exactly at n=2..40.")
if __name__=="__main__":
 lower_constants();upper()
