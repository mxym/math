import sympy as s
from itertools import product
from sympy.polys.matrices import DomainMatrix
I=s.eye(2)
vars=s.symbols("c:2")
G=[s.Matrix(2,2,[4,5,2,8]),s.Matrix(2,2,[3,7,13,11])]
cs={2:vars[-2],3:vars[-1]}
def neg(i):return i if i<2 else i^1
def ev(a,b):
 w=[x for i in range(4) for x in (a[i],neg(b[i]))]
 l=next(i for i,d in enumerate(w) if d<2)
 w=w[l:]+w[:l];n=0;M=I
 while n<8:
  k=w[n]
  if k<2:
   M=M*G[k];n+=1
  else:
   if n==7 or w[n+1]!=neg(k):return 0
   M=M*s.diag(cs[neg(k)],0);n+=2
 return s.expand(s.trace(M))
def orb(L,z):
 W=[]
 for a in product(range(4),repeat=4):
  if sorted(x for x in a if x>=2)!=L:continue
  b=a[1:]+a[:1];o=[a]
  while b!=a:o.append(b);b=b[1:]+b[:1]
  if min(o)==a and s.expand(z**len(o))==1:W.append(o)
 return W
for L,z,want in [([],1,6),([],-1,2),([],s.I,2),([],-s.I,2),([2,3],-1,10)]:
 W=orb(L,z)
 M=s.Matrix([[s.expand(sum(z**j*ev(a[0],b1) for j,b1 in enumerate(b))) for b in W] for a in W])
 F=s.QQ.algebraic_field(s.I) if z in [s.I,-s.I] else s.QQ.frac_field(*vars)
 D=DomainMatrix.from_Matrix(M).convert_to(F)
 rank=D.rank()
 print(L,z,len(W),rank)
 assert rank==want
