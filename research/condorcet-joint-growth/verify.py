"""Exact finite cross-checks; these are not evidence of the asymptotic error rate."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import factorial
def need(x,e):
 if not x: raise ValueError(e)
def exact_profiles(m,n):
 orders=list(permutations(range(n))); rows=[]
 for a in orders:
  rows.append([[int(a.index(x)<a.index(y)) for y in range(n)] for x in range(n)])
 total=0
 for order_indices in product(range(len(rows)),repeat=m):
  wins=[all(y==x or 2*sum(rows[i][x][y] for i in order_indices)>m for y in range(n)) for x in range(n)]
  need(sum(wins)<=1,'nonexclusive')
  total+=sum(wins)
 return F(total,len(orders)**m)
def conditional_moment(m,n):
 # For each of d opponents enumerate the subsets of favorable voters; integrate entire product over U.
 d=n-1; subs=[mask for mask in range(1<<m) if 2*mask.bit_count()>m]
 h=F()
 for a in product(subs,repeat=d):
  z=F(1)
  for i in range(m):
   k=sum(bool(M&(1<<i)) for M in a)
   z*=F(factorial(k)*factorial(d-k),factorial(d+1))
  h+=z
 return n*h
for m,n in [(1,4),(2,4),(3,4),(4,3),(5,3)]:
 q=exact_profiles(m,n);need(q==conditional_moment(m,n),('rank reduction',m,n));print('Q',m,n,q)
# Tilt fixed rational exp(a); compare whole finite conditional distribution at point, not just mean.
for r in [F(1),F(3,2),F(2),F(9)]:
 for u in [(F(1,3),F(4,5),F(3,4)),(F(1,4),F(2,5),F(2,7),F(1,2))]:
  m=len(u);h=[(1-z)*r+z/r for z in u]; q=[z/(r*y) for z,y in zip(u,h)]
  for v in product([0,1],repeat=m):
   a=b=c=F(1)
   for i,bit in enumerate(v):
    a*=u[i] if bit else 1-u[i]; b*=q[i] if bit else 1-q[i];c*=h[i]
   need(a==b*c*r**(2*sum(v)-m),'change of law')
  A,B=r,1/r
  if r!=1:need((1/A-1/B)/(B-A)==1,'environment tilt normalization')
print('PASS: all conditional tilted masses and affine normalization exact; no simulation.')
