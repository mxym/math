"""Checks against actual binomial coefficients; no floating point or external libraries."""
from math import comb
from functools import lru_cache

def ck(b,s):
 if not b:raise ArithmeticError(s)
def val(x):
 if not x:raise ValueError('zero')
 return (x&-x).bit_length()-1
def predicted(s,m):
 l=m.bit_length()-1
 return 2*((1<<s)-1) if m==1 else (1<<(s-l))-m.bit_count()+l

def rows():
 ncase=0
 for p in range(1,9):
  P=1<<p
  for multiple in range(1,7):
   N=multiple*P; z=[0]*P
   c=1
   for j in range(N):
    z[j%P]+=c;c=c*(N-1-j)//(j+1)
   for mask in range(0,P//2,2):
    W=sum(c for j,c in enumerate(z) if j&~mask==0)
    ck(val(W)==2*multiple-2+mask.bit_count(),('row',p,multiple,mask));ncase+=1
 print('direct binomial row/period/subcube cases:',ncase)

@lru_cache(None)
def prefix(b):
 # products of odd numbers in a period modulo 2^b
 q=1<<b; f=[1]
 for j in range(1,q+1): f.append((f[-1]*(j if j%2 else 1))%q)
 return f
def unitfac(n,b):
 q=1<<b;f=prefix(b);out=1
 while n:
  t,r=divmod(n,q);out=out*pow(f[-1],t,q)*f[r]%q;n//=2
 return out
def binmod(n,j,b):
 if j<0 or j>n:return 0
 d=j.bit_count()+(n-j).bit_count()-n.bit_count()
 if d>=b:return 0
 q=1<<b
 return ((1<<d)*unitfac(n,b)*pow(unitfac(j,b)*unitfac(n-j,b),-1,q))%q
def selftest():
 for n in range(70):
  for j in range(n+1):
   for b in (1,2,3,7,10):
    ck(binmod(n,j,b)==comb(n,j)%(1<<b),('binmod',n,j,b))
def directfamily():
 cases=0
 for a in (2,3,4):
  for s in range(4):
   for i in range(max(2,s+1),11):
    A=1<<a;L=1<<s;D=1<<(a+i-s)
    for r in (0,1):
     n=A*((1<<i)-1)+r
     if n>4500:continue
     z=[1]
     for j in range(n):z.append(z[-1]*(n-j)//(j+1))
     for m in range(1,L+1,2):
      V=predicted(s,m)+r; k=m*D-A
      # The proof only needed i-s > predicted v(W), not the stated uniform bound.
      if k<1 or i-s<=V or V+1>=n:continue
      W=sum(x for j,x in enumerate(z) if j&k==k)
      ck(val((1<<n)-2*W)==V+1,('direct',a,s,i,m,r));cases+=1
 print('direct integer original-weight cases (including parameter stress):',cases)
def huge():
 cases=0; high=0
 for s in range(7):
  L=1<<s
  for m in range(1,L+1,2):
   for r in (0,1):
    V=predicted(s,m)+r
    if V>16:continue
    for a,i in [(2,2*L+s),(3,2*L+s+1)]:
     A=1<<a;D=1<<(a+i-s);n=A*((1<<i)-1)+r;k=m*D-A
     # Enumerate every free submask directly in the original j coordinates, including
     # the non-anchor terms (no valuation-based deletion).
     free=((1<<n.bit_length())-1)^k; v=free; W=0; mod=1<<(V+1)
     while True:
      j=k|v
      if j<=n:W=(W+binmod(n,j,V+1))%mod
      if not v:break
      v=(v-1)&free
     ck(W==1<<V,('original-mod',a,i,s,m,r,V,W)); cases+=1;high=max(high,n.bit_length())
 print('direct mod 2^b sums within the conjectured domain:',cases,'largest n bitlength:',high)
if __name__=='__main__':
 rows();selftest();directfamily();huge()
