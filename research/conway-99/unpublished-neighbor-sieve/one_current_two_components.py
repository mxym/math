"""B12 affine-recovery inventory, using only exact integer/rational operations."""
from itertools import combinations
from collections import Counter
from fractions import Fraction

def rank(A):
 A=[[Fraction(x) for x in row] for row in A];r=0
 for j in range(len(A[0])):
  i=next((i for i in range(r,len(A)) if A[i][j]),None)
  if i is None:continue
  A[i],A[r]=A[r],A[i]
  for i in range(r+1,len(A)):
   q=A[i][j]/A[r][j];A[i]=[a-q*b for a,b in zip(A[i],A[r])]
  r+=1
 return r
P=(1,0,3,2);Q=(2,3,0,1);f=(0,3,2,1)
N=[set() for _ in range(12)]
for i in range(4):
 for a,b in [(i,P[i]),(4+i,4+Q[i]),(8+i,8+P[i]),(i,4+i),(4+i,8+i),(8+i,f[i])]:N[a].add(b);N[b].add(a)
h=(2,1,5,6,0,0,0,0,5,6,2,1)
assert sum(h)%7==0 and all((3*h[i]-sum(h[j] for j in N[i]))%7==0 for i in range(12))
M={(i,j):2-int(j in N[i])-len(N[i]&N[j])-int(i//4==j//4) for i,j in combinations(range(12),2)}
hist=Counter();E0=[]
for (i,j),n in M.items():
 assert n>=0
 a=(-(h[i]+h[j]))%7;hist[a]+=n
 if a==0 and n:E0.append((i,j));assert n==1
assert [hist[i] for i in range(7)]==[10,12,9,4,4,9,12]
assert E0==[(0,2),(1,3),(1,9),(3,11),(4,5),(4,7),(5,6),(6,7),(8,10),(9,11)]
E1=[(0,3),(0,5),(0,6),(1,8)]
assert all(M[e]==1 and sum(h[i] for i in e)%7 for e in E1)
B=lambda E:[[int(i in e) for e in E] for i in range(12)]
assert rank(B(E0))==8 and rank(B(E0+E1))==12
# Kernel directions are the two alternating cycle edge vectors, zero at extra edges.
for cyc in [(1,3,11,9),(4,5,6,7)]:
 k={tuple(sorted((cyc[i],cyc[(i+1)%4]))):(-1)**i for i in range(4)}
 assert all(sum(int(i in e)*k.get(e,0) for e in E0+E1)==0 for i in range(12))
print("B12 current distribution:",[hist[i] for i in range(7)])
print("14 omitted pair tags:",E0+E1,"; incidence rank 12; 46 specified nonzero words remain.")
