import itertools,functools
from sympy import QQ
from sympy.polys.matrices import DomainMatrix
F=QQ.frac_field(*[f'{typ}{j}' for typ in 'cude' for j in range(1,5)])
V=F.gens; zero=F.zero;one=F.one
c=(zero,)+V[:4];u=(zero,)+V[4:8];d=(zero,)+V[8:12];e=(zero,)+V[12:16]
q=5
A={0:[(0,0,one)]};D={0:[(i,0,u[i]) for i in range(1,q)]}
for i in range(1,q):
 j=(-i)%q
 A[i]=[(0,i,one),(j,0,c[i])]
 D[i]=[(i,i,d[i]),(j,j,e[i])]
@functools.lru_cache(None)
def trace_coefficient(row,col,k):
 seq=sum(zip(row,col),())
 value=zero
 for hits in itertools.combinations(range(8),k):
  walks=[(i,i,one) for i in range(q)]
  for pos,label in enumerate(seq):
   steps=D[label] if pos in hits else A[label]
   walks=[(start,end,val*edge) for start,mid,val in walks for tail,end,edge in steps if mid==tail]
  value+=sum((v for i,j,v in walks if i==j),zero)
 return value
def orbs(words):
 out=[]
 for x in sorted(words):
  o=[x]
  while (y:=o[-1][1:]+o[-1][:1])!=x:o.append(y)
  if min(o)==x and len(o)%2==0:out.append(o)
 return out
def mat(R,C,k):
 # For this script orbit size always four.
 return DomainMatrix.from_list([[sum(((-1)**j*trace_coefficient(r[0],w,k) for j,w in enumerate(o)),zero) for o in C] for r in R],F)
def oms(x):return orbs(set(itertools.permutations(x)))
K=oms((1,2,3,4))
E1=oms((0,0,1,4)); E2=oms((0,0,2,3))
def null(E):
 B=mat(E,E,0).to_list()
 v=[zero]*3
 for a,b in itertools.combinations(range(3),2):
  if B[a][b]:
   j=3-a-b
   v[a]=B[b][j];v[b]=-B[a][j];v[j]=B[a][b];break
 assert all(sum((x*y for x,y in zip(row,v)),zero)==zero for row in B)
 return DomainMatrix.from_list([[z] for z in v],F)
U=null(E1);V0=null(E2)
print('null',U.to_list(),V0.to_list(),flush=True)
H=mat(K,K,2);B=mat(K,E1,2)*U;C=mat(K,E2,2)*V0
for x in (1,2,3,4):
 T=oms((0,)+tuple(j for j in (1,2,3,4) if j!=x))
 # Without negating columns the block pairs to the opposite block.
 W=oms(tuple((-j)%q for j in T[0][0]))
 G=mat(T,W,0)
 Z=mat(K,W,1)*G.inv()
 H-=Z*mat(T,K,1)
 B-=Z*mat(T,E1,1)*U
 C-=Z*mat(T,E2,1)*V0
 print('computed',x,flush=True)
h=H.to_list();b=[v[0] for v in B.to_list()];g=[v[0] for v in C.to_list()]
for j,row in enumerate(h):
 for i,v in enumerate(row):assert v==-h[i][j]
# Modulo Pfaffian numerator; no denominator need.
D=[row+[x,y] for row,x,y in zip(h,b,g)]+[[-x for x in b]+[zero,zero],[-x for x in g]+[zero,zero]]
@functools.lru_cache(None)
def pf(Js):
 if not Js:return one
 return sum(((-1)**(i+1)*D[Js[0]][j]*pf(Js[1:i]+Js[i+1:]) for i,j in enumerate(Js[1:],1) if D[Js[0]][j]),zero)
print('support',[tuple(i for i,x in enumerate(row) if x) for row in D],flush=True)
assert pf(tuple(range(8)))==zero
print('Exact effective quadratic cross-pair coefficient is zero.',flush=True)
