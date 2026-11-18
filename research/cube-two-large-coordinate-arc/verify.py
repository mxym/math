"""Exact integer/rational verification; Python 3, no nonstandard dependencies or asserts."""
from fractions import Fraction as Q
from math import comb, factorial, lcm
from itertools import pairwise
from time import perf_counter

def want(b,msg):
 if not b: raise ValueError(msg)
def trim(p):
 while len(p)>1 and p[-1]==0:p.pop()
 return p
def add(*ps):
 a=[0]*max(map(len,ps))
 for p in ps:
  for j,x in enumerate(p):a[j]+=x
 return trim(a)
def sc(p,s):return [s*x for x in p]
def mon(p,n=1): return [0]*n+p
def der(p):
 return [i*x for i,x in enumerate(p) if i] or [0]
def val(p,x):
 v=0
 for c in reversed(p):v=c+x*v
 return v
def norm(p):
 d=lcm(*(Q(x).denominator for x in p))
 return [int(x*d) for x in p]
def shift(p,x):
 # Taylor coefficients of p(x+u), using Horner without binomial tables
 a=[0]*len(p)
 for j in range(len(p)-1,-1,-1):
  for k in range(j,len(p)-1):a[k]+=x*a[k+1]
  a[j]+=p[j]
 return a
def desc(p,L,H):
 # coefficients of (1+u)^d p((L+Hu)/(1+u)); deltas are positive.
 p=trim(list(p));d=len(p)-1;q=shift(p,L)
 if H is None:return q  # p(L+u) instead
 q=[x*(H-L)**i for i,x in enumerate(q)]
 a=[0]*(d+1)
 for j,x in enumerate(q):
  row=1
  for k in range(d-j+1):
   a[k+j]+=row*x;row=row*(d-j-k)//(k+1)
 return a
def variations(a):
 signs=[1 if x>0 else -1 for x in a if x!=0]
 want(signs,'identically zero polynomial')
 return sum(x!=y for x,y in pairwise(signs))
def poly_shift_power(k,c):return [comb(k,j)*c**(k-j) for j in range(k+1)]
def finite(m):
 def cdfpoly(k,x):
  return add(*(sc(poly_shift_power(k,m-2*l),(-1)**l*comb(m,l)) for l in range(m+1) if x+m-2*l>=0))
 aa=val(cdfpoly(m,0),0);bb=val(cdfpoly(m+1,0),0)
 knots=[2]+[x for x in range(3,m+1) if (x+m)%2==0]
 roots=0
 for i,L in enumerate(knots):
  H=knots[i+1] if i+1<len(knots) else None
  A=cdfpoly(m,L);B=cdfpoly(m+1,L)
  V=add(sc(mon(A),m+1),sc(B,-1),[bb])
  D=add(mon(V,2),sc(V,4*m),sc(mon(add(A,[-aa])),-2*m*(m+1)))
  if i==0:want(val(D,2)==0,('main diagonal',m))
  if i and val(D,L)==0:roots+=1
  cert=desc(D,L,H)
  if not i:want(next(c for c in cert if c)<0,('left endpoint sign',m))
  if H is None:want(cert[-1]>0,('ray sign',m))
  if m==2 and H is None:want(val(D,4)==0,'known n=4 root x=4')
  v=variations(cert)
  want(v<=1,('inconclusive',m,L,H,v));roots+=v
 want(roots==1,('nontrivial root count',m,roots))
 return len(knots)
def large():
 # Certified polynomial replacement of sqrt(2pi) Edgeworth approximant; z in [0,196].
 N=400
 err=[Q(98**(N-j+1),2**j*factorial(N-j+1)) for j in range(3)]
 want(1000*max(err)<Q(1,10**9),'Taylor error')
 T=[Q((-1)**j,2**j*factorial(j)) for j in range(N+1)]
 M=64; cases=0
 for h in [Q(0),Q(1,M)]:
  S=add(sc(T,1-Q(3,20)*h),sc(mon(T),Q(3,10)*h),sc(mon(T,2),-h/20))
  K=add([c*Q(6*j,(j+1)*(2*j+1)) for j,c in enumerate(S)],
        mon([c/Q(2*j+2) for j,c in enumerate(S)]))
  parts=[(0,1,2,-1,Q(1,400)),(1,20,0,-1,Q(1,300)),(20,36,1,1,Q(3,500)),(36,196,0,1,Q(1,64))]
  for L,R,j,sign,margin in parts:
   p=K[:]
   for _ in range(j):p=der(p)
   p=norm(add(sc(p,sign),[-margin]))
   coeff=desc(p,L,R)
   # strictly positive Bernstein/Descartes coefficients certify closed-interval bound
   want(min(coeff)>0,('sign certificate',h,L,R,j,sign,margin,sum(x<=0 for x in coeff)))
   cases+=1
 def rem(j,t):
  return [(Q(12+t,2)+6)/2, Q(1,4)+Q(13,4)*(Q(12+t,8)+1), Q(13,16)+31*(Q(12+t,72)+Q(1,10))][j]/M**2
 for L,R,j,sign,margin in parts:
  want(rem(j,R)+Q(1,10**6)<margin,('error margin',L,R,j))
 return cases
if __name__=='__main__':
 start=perf_counter()
 want(shift([1,2,3],5)==[86,32,3],'Taylor-shift self-test')
 want(desc([1,2,3],2,5)==[17,76,86],'Mobius self-test')
 count=sum(finite(m) for m in range(2,64))
 print('PASS: exactly one open-arc root in each of 62 finite dimensions; checked',count,'polynomial cells, including the infinite tails.',flush=True)
 print('PASS:',large(),'high-dimensional signed polynomial certificates and analytic remainder budgets.',flush=True)
 print('Elapsed seconds:',round(perf_counter()-start,2))
