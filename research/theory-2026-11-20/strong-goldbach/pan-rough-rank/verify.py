from math import factorial as fac,comb,prod
from fractions import Fraction as F
from itertools import combinations

kappa=F(333,4000)
def ceil(n,d):return (n+d-1)//d
def exact(j,K):
 a=kappa.denominator-j*kappa.numerator; H=kappa.denominator*K; c=kappa.numerator*K
 ans=0; cnt=0;vol=0
 EU=[sum((-1)**i*comb(j,i)*(l-i)**(j-1) for i in range(l+1)) for l in range(j+1)]
 def visit(B,l):
  nonlocal ans,cnt,vol
  cnt+=1; mult=fac(j)
  for b in set(B):mult//=fac(B.count(b))
  v=mult*EU[l];vol+=v
  r=[c+a*b for b in B];den=prod(r);rmax=r[0]
  if j==6:
   # F <= binomial(4,2) min x_i; cancels the smallest factor
   eig=ceil(6*H**6,den//r[-1]*rmax)
  elif j==7:
   n2=sum(2*(r[i]+r[t]+a*min(l,2))>=H for i,t in combinations(range(j),2))
   n3=sum(2*(r[i]+r[t]+r[u]+a*max(0,l-4))>H for i,t,u in combinations(range(j),3))
   f=max(0,min(10,10+n2-n3))
   # prod x >= prod low_i * (1 + (sum x-sum low)/max low).
   eig=ceil(f*H**(j+1),den*(rmax+a*l))
  else:raise ValueError
  ans+=v*eig
 def rec(B,remain,slots,cap,l):
  if slots==0:
   if remain==0:visit(B,l)
   return
  for n in range(ceil(remain,slots),min(cap,remain)+1):
   rec(B+[n],remain-n,slots-1,n,l)
 for l in range(1,j):
  rec([],K-l,j,K-l,l)
 expected=K**(j-1)
 if vol!=expected:raise RuntimeError((vol,expected))
 ans=F(4*a**(j-1)*ans, H**(j-1)*fac(j)*fac(j-1))
 print('rank',j,'grid',K,'cells',cnt,'upper',str(ans),flush=True)
 return ans
def tail(j):
 k=kappa;C=comb(j-2,(j-2)//2)
 if j%2==0: C=F(C,j)
 return 4*C*(1/k-j)**(j-1)/((1-(j-1)*k)*fac(j-1)**2)
if __name__=='__main__':
 # Every comparison influencing acceptance is exact rational/integer arithmetic.
 # No asserts: python -O must execute and reject by exactly the same criteria.
 s6=exact(6,64)
 s7=exact(7,64)
 tails=[tail(j) for j in range(8,13)]
 if not s6<F(259,1000) or not s7<F(172,1000):
  raise ArithmeticError("rank-six/seven rational bounds failed")
 tailtotal=sum(tails)
 if tailtotal>=F(18,1000): raise ArithmeticError("rational tail too large")
 total=s6+s7+tailtotal
 if total>=F(448,1000): raise ArithmeticError("total is not below 0.448")
 print('tail',tailtotal,'single_oriented_total',total,'both orientations < 0.896 (limsup)')
