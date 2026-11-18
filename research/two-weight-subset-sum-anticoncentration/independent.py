"""Integer-only support/collision and modular tests; no dependency, works under -O."""
from math import comb,gcd
def check(x):
 if not x: raise ValueError('failed')
def add(P,d):
 # polynomial convolution against 1+x**d, using coefficient recurrence
 Q=P+[0]*d
 for i,x in enumerate(P):Q[i+d]+=x
 return Q
def residue(d,j):
 a=[0]*d;a[0]=1
 for k in range(j):a=[a[i]+a[(i-1)%d] for i in range(d)]
 return max(a)
for d in range(2,51):
 b=residue(d,d);z=residue(d,2*d)
 check(b==comb(d,d//2))
 check(z==2+comb(2*d,d))
 check(2*d*z*z<=1<<(4*d))
 r=1
 for j in range(1,2*d+6):
  q=residue(d,j);check(q<=2*r);r=q
for j in range(1,1001):
 q=comb(j,j//2)**2;D=1<<(2*j)
 check(4*(j+1)*q<=3*D and 3*(2*j+1)*q<4*D and (j+2)*q<=D)
cnt=0;branches=[0]*4
for b in range(2,19):
 for a in range(1,b):
  if gcd(a,b)!=1:continue
  A=[1]
  for n in range(1,33):
   A=add(A,a);P=A
   for m in range(1,33):
    P=add(P,b);K=sum(x!=0 for x in P);M=max(P)
    check(sum(P)==1<<(m+n))
    check(K==(m+1)*(n+1)-max(0,m-a+1)*max(0,n-b+1))
    check(K*M*M<1<<(2*(m+n)))
    branches[0 if (m<a or n<b) else 1 if a>1 else 2 if n<2*b else 3]+=1;cnt+=1
print('PASS: d=2..50 exact residue peaks at d,2d, decay; j=1..1000 central-binomial constants')
print('PASS:',cnt,'coprime two-weight cases (a<b<=18, 1<=n,m<=32); full polynomial support and strict peak bound')
print('Branches: injective, both moduli >=2, unit modulus near endpoint, unit modulus far endpoint:',*branches)
