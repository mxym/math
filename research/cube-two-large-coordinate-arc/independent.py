"""Independent verifier. Does not import the author's code; all signs use integers/rationals."""
if not __debug__:
 raise SystemExit("Refusing optimized Python: independent verification requires assertions enabled.")
from math import comb, factorial, lcm, prod
from fractions import Fraction as F
from collections import Counter
from itertools import pairwise
def add(p,q):
 return [(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))]
def cp(p,c): return [i*c for i in p]
def poly(a,b,k):return [comb(k,j)*a**(k-j)*b**j for j in range(k+1)]
def mul(p,q):
 r=[0]*(len(p)+len(q)-1)
 for j,x in enumerate(p):
  if x!=0:
   for i,y in enumerate(q):r[j+i]+=x*y
 return r
def signed(a):return [1 if x>0 else -1 for x in a if x]
def var(a):
 z=signed(a)
 if not z:raise ArithmeticError('identically zero')
 return sum(x!=y for x,y in pairwise(z))
def cells(m):
 C=2**(m-1)*factorial(m)
 b0=sum((-1)**i*comb(m,i)*max(m-2*i,0)**(m+1) for i in range(m+1))
 knots=sorted({2}|{i for i in range(3,m+1) if (i-m)%2==0})
 ct=rm=rc=0;endroot=0
 # On the finite barycentric cells use the polynomials in the two endpoint linear forms directly.
 for l,h in pairwise(knots):
  a=[0]*(m+1);b=[0]*(m+2);v=[l,h];w=[1,1];v2=mul(v,v);w2=[1,2,1]
  for i in range(m+1):
   s=m-2*i
   if l+s<0:continue
   p=cp(poly(l+s,h+s,m),(-1)**i*comb(m,i))
   a=add(a,p);b=add(b,mul(p,[l+s,h+s]))
  # Original D scaled by (m+1)C = (m+1)x(x²+2m)A − (x²+4m)B + B0(x²+4m)+2m(m+1)Cx.
  aterm=cp(mul(mul(v,add(v2,cp(w2,2*m))),a),m+1)
  bterm=mul(add(v2,cp(w2,4*m)),add(cp(b,-1),cp(poly(1,1,m+1),b0)))
  cterm=cp(mul(v,poly(1,1,m+2)),2*m*(m+1)*C)
  r=add(add(aterm,bterm),cterm);nu=var(r)
  assert len(r)==m+4 and nu<=1
  if l==2:assert not r[0] and signed(r)[0]<0
  elif not r[0]:endroot+=1
  if ct:assert prev==r[0]
  prev=r[-1];rc+=nu;ct+=1
 # The support ends at m; from here the full moment M= B0/[(m+1)C] is constant and F=1.
 l=knots[-1];q=[b0*(l*l+4*m)-2*m*(m+1)*C*l,2*b0*l-2*m*(m+1)*C,b0]
 if ct:assert prev==q[0]
 if l==2:assert q[0]==0 and signed(q)[0]<0
 elif q[0]==0:endroot+=1
 assert q[-1]>0
 nr=var(q);assert rc+nr+endroot==1
 return ct+1,rc,nr,endroot

def homogenized_horner(coef,lo,hi):
 n=len(coef)-1
 # Apply Horner's rule directly in two homogeneous arguments, no translations of the Taylor coefficients.
 a=[coef[-1]];row=[1]
 for i in range(n-1,-1,-1):
  a=mul(a,[lo,hi]);row=mul(row,[1,1]);a=[x+coef[i]*y for x,y in zip(a,row)]
 return a

def large():
 fac=lambda n,j:prod(range(n-j+1,n+1))
 for w in (F(0),F(1,64)):
  # Gaussian with Hermite correction. Integrate monomials directly.
  c=[F((-1)**i,2**i*factorial(i)) for i in range(401)]
  hcoef=mul(c,[1-3*w/20,6*w/20,-w/20])
  k=[F(0)]*(len(hcoef)+1)
  for i,g in enumerate(hcoef):
   k[i]+=g*(F(12,2*i+2)-F(6,2*i+1))
   k[i+1]+=g*F(1,2*i+2)
  while not k[-1]:k.pop()
  for l,h,j,sg,e in ((0,1,2,-1,F(1,400)),(1,20,0,-1,F(1,300)),(20,36,1,1,F(3,500)),(36,196,0,1,F(1,64))):
   a=[sg*fac(i,j)*k[i] for i in range(j,len(k))];a[0]-=e
   den=lcm(*(x.denominator for x in a))
   a=[int(x*den) for x in a]
   r=homogenized_horner(a,l,h)
   assert r and min(r)>0 and len(r)==len(a)
   budget=[F(1,2)*(F(12+h,2)+6),F(1,4)+F(13,4)*(F(12+h,8)+1),F(13,16)+31*(F(12+h,72)+F(1,10))][j]*F(1,64**2)+F(1,10**6)
   assert e>budget
   print(f'h={w} t=[{l},{h}] derivative={j}: all {len(r)} coefficients strictly positive; certified leftover {e-budget}')
 for j,M in [(0,F(1,2)),(2,F(13,4)),(4,F(31))]:
  v=F(27,1500)*prod(range(1,j+6,2))+F(1,800)*prod(range(1,j+8,2))+F(2,1000);assert v<M
  print('Fourier derivative',j,'cap with tails',v,'<',M)
 for j in range(3):assert F(98**(401-j),2**j*factorial(401-j)) < F(1,10**12)
if __name__=='__main__':
 d=Counter();mkt=[];rays=[]
 for m in range(2,64):
  n,c,r,z=cells(m);d.update(dict(cells=n,in_bounded_cell=c,on_ray=r,at_knot=z))
  if z:mkt.append(m)
  if r:rays.append(m)
 print('Finite exact counts:',dict(d),'positive knot for m=',mkt,'infinite cell for m=',rays,flush=True)
 large()
