from itertools import combinations
from math import gcd,isqrt
from fractions import Fraction
def check(n,k,p,m,mod):
 assert gcd(p,n)==gcd(p,k)==1 and k*m<p and n<(p+k)*(m+1)
 assert (n-k*(m+1))%p==0 and all((n-h*(m+1))%p or n<h*(m+1) for h in range(n+1) if h!=k)
 z=next(x for x in range(2,mod) if pow(x,p,mod)==1)
 zs=[pow(z,i,mod) for i in range(p)]
 assert len(set(zs))==p
 w=[]
 for x in range(p):
  y=1
  for u in range(m): y=y*(zs[x]-zs[u])%mod
  w.append(y)
 c=1
 for u in range(m):c=c*(-zs[u])%mod
 target=p*pow(c,k,mod)%mod
 count=0
 for sites in combinations(range(n),k):
  value=0
  for x in range(p):
   wgt=1
   for j,t in enumerate(sites):wgt=wgt*w[(x+t-j*(m+1))%p]%mod
   value+=wgt
  assert value%mod==target!=0
  count+=1
 print(n,k,p,m,count)
check(13,2,7,2,1009)
check(23,3,11,3,397)
for k in [1,2,3,4,5]:
 for n in [10**i+j for i in range(32,47,2) for j in [0,1,42,371]]:
  a,b=10*k+1,10
  q0=max(1,isqrt(n*b//a))
  while q0%k!=n%k or a*q0*q0<b*n:q0+=1
  p0=1+((a*q0-b+ b*k*a-1)//(b*k*a))*(k*a)
  gamma=Fraction(k*b,a)/2+Fraction(1,2)
  def data(j):
   p,q=p0+k*a*j,q0-k*b*j
   return p,q,n-p*q
  def crosses(j):
   p,q,R=data(j)
   return R>=gamma*p
  l,h=0,1
  while not crosses(h):h*=2
  while h-l>1:
   j=(h+l)//2
   if crosses(j):h=j
   else:l=j
  j=h
  p,q,R=data(j)
  while gcd(p,n)!=1:
   j+=1
   p,q,R=data(j)
  if n>=10**32:
   m=R//k-1
   assert R%k==0 and k<p and (n-k*(m+1))%p==0 and gcd(p,k)==1 and k*m<p and n<(p+k)*(m+1) and m>=1,(k,n,p,q,R)
print("All sampled large parameters pass")
