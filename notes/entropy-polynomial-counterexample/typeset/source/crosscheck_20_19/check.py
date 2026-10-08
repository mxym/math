from fractions import Fraction as F
from math import comb
import json

if not __debug__:
 raise SystemExit("Run this verifier without Python -O or -OO.")

def coefficients(k,r):
 return [sum((F((-1)**(j-v)*comb(r*v+k,k)*comb(k,j-v),v+1) for v in range(j+1)),F(0)) for j in range(k)]
def H(k,r,x):
 c=coefficients(k,r); t=x**r; y=F(0)
 for a in c[::-1]: y=y*t+a
 return y

def alpha_interval(k,r):
 lo,hi=F(0),F(1)
 for _ in range(100):
  t=(lo+hi)/2
  if t**r*(1+t)**(k-r)<1:lo=t
  else:hi=t
 assert lo**r*(1+lo)**(k-r)<1<hi**r*(1+hi)**(k-r)
 return lo,hi

def check(k,r,xs):
 lo,hi=alpha_interval(k,r)
 out=[]
 for x in xs:
  a=k*(1-x**r)**k*H(k,k,x)
  b=r*(1-x**k)**k*H(k,r,x)
  assert a>0
  pl,pu=a*lo-b,a*hi-b
  sign=1 if pl>0 else -1 if pu<0 else 0
  assert sign!=0
  out.append({'x':str(x),'sign':sign,'lower_sign':(pl>0)-(pl<0),'upper_sign':(pu>0)-(pu<0)})
 assert [a['sign'] for a in out]==[1,-1,1,-1,1]
 return {'k':k,'r':r,'alpha_lo':str(lo),'alpha_hi':str(hi),'points':out}
res=check(20,19,[F(1,5),F(2,5),F(11,20),F(13,20),F(3,4)])
print(json.dumps(res,indent=2))
