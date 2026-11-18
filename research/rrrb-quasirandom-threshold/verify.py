from fractions import Fraction as Q
from itertools import product
from random import Random
def multiply(A,B):return [[sum(a*b for a,b in zip(row,col))for col in zip(*B)] for row in A]
def sc(a,x):return [[a*y for y in z] for z in x]
def add(A,B):return [[a+b for a,b in zip(i,j)]for i,j in zip(A,B)]
def tr(A):return sum(A[i][i]for i in range(len(A)))
def inn(a,b):return sum(x*y for x,y in zip(a,b))
rng=Random(7)
for n in range(2,7):
 for k in range(6):
  W=[[0]*n for _ in range(n)]
  for i in range(n):
   for j in range(i+1):W[i][j]=W[j][i]=Q(rng.randrange(6),5)
  T=sc(Q(1,n),W)
  degree=[sum(r) for r in T];p=sum(degree)/n;u=[v-p for v in degree]
  A=[[T[i][j]-(u[i]+u[j]+p)/n for j in range(n)]for i in range(n)]; AA=multiply(A,A); Au=[inn(row,u) for row in A]
  q=inn(u,u)/n; E=inn(u,Au)/n
  excess=(2*p-4*p*p)*q+(1-4*p)*E-4*inn(Au,Au)/n-2*q*q-tr(multiply(AA,AA))
  F=sum(W[i][j]*W[j][k]*W[k][l]*(1-W[l][i])for i,j,k,l in product(range(n),repeat=4))/n**4
  assert excess==F-p**3*(1-p)
  if q:
   lam=E/q
   assert excess<=q*(2*p-4*p*p+(1-4*p)*lam-4*lam**2)-2*q**2-lam**4
print('30 exact rational kernels: direct 4-tuple / block expansion & upper bound PASS')
# Cross-check finite normalization: three UNORIENTED cyclic edge sets on each 4-subset.
from itertools import combinations, permutations
for n in range(4,13):
 G={e for e in combinations(range(n),2) if rng.randrange(2)}
 def red(i,j):return tuple(sorted((i,j))) in G
 lab=sum(red(i,j) and red(j,k) and red(k,l) and not red(l,i)
         for i,j,k,l in permutations(range(n),4))
 un=0
 for a,b,c,d in combinations(range(n),4):
  for cyc in [[a,b,c,d],[a,b,d,c],[a,c,b,d]]:
   un+=sum(red(cyc[i-1],cyc[i]) for i in range(4))==3
 assert lab==2*un
print('9 finite simple graphs: injections = 2 × undirected RRRB cycles PASS')
# Exact calculation over Q(sqrt(d)). Compare algebraic identities, not rounded decimals.
def K(a,b=0):return (Q(a),Q(b))
def plus(a,b):return (a[0]+b[0],a[1]+b[1])
def times(a,b):return (a[0]*b[0]+d*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def neg(a):return (-a[0],-a[1])
def minus(a,b):return plus(a,neg(b))
def sq(a):return times(a,a)
def scale(a,k):return (a[0]*k,a[1]*k)
d=2;c=K(4,2);x2=K(4,-2)
assert times(minus(c,K(1)),x2)==c  # Critical x²=c/(c−1).
assert plus(times(minus(K(1),x2),c),x2)==K(0)  # 4c[a+x²/(4c)]=0 at the threshold
d=5;r=K(Q(3,8),Q(-1,8));C=minus(r,scale(sq(r),4));q=scale(C,Q(1,4))
assert q==K(Q(-1,8),Q(1,16))
assert plus(minus(K(1),scale(r,12)),scale(sq(r),16))==K(0)
excess=minus(scale(sq(C),Q(1,8)),sq(sq(r)))
assert plus(K(Q(1,16)),excess)==K(Q(21,512),Q(5,512))
print('sharp threshold radical, centre optimum radical & derivative identities PASS')
