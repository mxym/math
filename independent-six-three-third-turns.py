#!/usr/bin/env python3
"""Independent audit: exact rank-six root closure and 60/57 witness pair tests."""
if not __debug__:
    raise RuntimeError('run normal Python without -O')
from itertools import product, combinations
from fractions import Fraction as F
tpts=((2,0),(-1,1),(-1,-1))
axis=((3,1),(0,2),(-3,1),(-3,-1),(0,-2),(3,-1))
T={tuple(y for c in w for y in c) for w in product(tpts,repeat=3)}
E=T|{tuple(-x for x in a) for a in T}
for k in range(3):
 for a,b in axis:
  E.add(tuple(a if i==2*k else b if i==2*k+1 else 0 for i in range(6)))
def dot(a,b):return sum(x*y*(3 if i%2 else 1) for i,(x,y) in enumerate(zip(a,b)))
assert len(T)==27 and len(E)==72
assert all(dot(x,x)==12 for x in E)
for x,y in combinations(E,2):assert dot(x,y) in (-12,-6,0,6)
for x,y in product(E,repeat=2):
 d=dot(x,y)
 assert d%6==0
 assert tuple(a-d//6*b for a,b in zip(x,y)) in E
def main_component(E):
 S={next(iter(E))}
 while True:
  S1=S|{y for x in S for y in E if dot(x,y)}
  if S1==S:return S
  S=S1
assert main_component(E)==E
assert axis[0][0]*axis[1][1]-axis[1][0]*axis[0][1] != 0
diff={tuple(a-b for a,b in zip(x,y)) for x,y in product(T,repeat=2) if dot(x,y)==6}
assert len(diff)==18 and diff<=E
print('Independent root model:',len(E),'points,',len(E)**2,'ordered reflections,',len(diff),'completion roots')
# Witness: store radius squares and angles in units of pi/6; no floating-point comparison.
rad=[(F(1),F(0),F(0)),(F(1,3),F(2,3),F(0)),(F(1,3),F(0),F(2,3)),(F(0),F(1,2),F(1,2))]
phase=[(0,0,0),(1,0,0),(1,0,0),(0,1,1)]
C=[(F(1),F(0)),(F(0),F(1,2)),(F(1,2),F(0)),(F(0),F(0)),(F(-1,2),F(0)),(F(0),F(-1,2)),(F(-1),F(0))]
C=C+C[-2:0:-1]
assert len(C)==12
W=set()
for k in range(4):
 for shift in product(range(3),repeat=3):
  for sign in range(2):
   W.add((k,tuple((phase[k][i]+4*shift[i]+6*sign)%12 if rad[k][i] else 0 for i in range(3))))
assert len(W)==60
def sg(u,v):
 if not u or not v:return ((u+v)>0)-((u+v)<0)
 if u*v>0:return 1 if u>0 else -1
 a=u*u-3*v*v
 return ((a>0)-(a<0))*(1 if u>0 else -1)
for (k,a),(l,b) in combinations(W,2):
 ords=[i for i in range(3) if rad[k][i]*rad[l][i]]
 if k==l:
  u=sum(rad[k][i]*C[(a[i]-b[i])%12][0] for i in ords)-F(1,2)
  v=sum(rad[k][i]*C[(a[i]-b[i])%12][1] for i in ords)
  assert sg(u,v)<=0
 elif ords:
  assert len(ords)==1
  i=ords[0];u,v=C[(a[i]-b[i])%12]
  assert sg(u,v)<=0 or rad[k][i]*rad[l][i]*(u*u+3*v*v)<=F(1,4)
assert rad[1][0]==rad[2][0]==F(1,3) and phase[1][0]==phase[2][0]
assert (1,phase[1]) in W and (2,phase[2]) in W
assert F(1,3)*12 not in (-12,-6,0,6)
print('Independent witness: 1770 exact pair inequalities, nonroot product 1/3')

# Independent 57-point, precisely one triple orbit. Angles in units of pi/12.
rad57=[(F(1,3),)*3,(F(1),F(0),F(0)),(F(1,2),F(1,2),F(0)),(F(1,2),F(0),F(1,2)),(F(0),F(1,2),F(1,2))]
phase57=[(0,0,0),(2,0,0),(5,4,0),(5,0,4),(0,4,4)]
W57=set()
for k in range(5):
 for sh in product(range(3),repeat=3):
  W57.add((k,tuple((phase57[k][i]+8*sh[i])%24 if rad57[k][i] else 0 for i in range(3))))
assert len(W57)==57
# Exact coefficients of 1, sqrt2, sqrt3, sqrt6.
def c57(j):
 w=min(j%24,(-j)%24)
 return [(F(1),0,0,0),(0,F(1,4),0,F(1,4)),(0,0,F(1,2),0),(0,F(1,2),0,0),(F(1,2),0,0,0),(0,F(-1,4),0,F(1,4)),(0,0,0,0),(0,F(1,4),0,F(-1,4)),(F(-1,2),0,0,0),(0,F(-1,2),0,0),(0,0,F(-1,2),0),(0,F(-1,4),0,F(-1,4)),(F(-1),0,0,0)][w]
def add4(a,b):return tuple(x+y for x,y in zip(a,b))
def mul4(a,b):
 r=[F(0)]*4
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i^j]+=x*y*(2 if i&j&1 else 1)*(3 if i&j&2 else 1)
 return tuple(r)
def scl(a,x):return tuple(x*y for y in a)
def sgn4(a):
 u=(a[0],a[2]);v=(a[1],a[3])
 su=sg(*u);sv=sg(*v)
 if not su or not sv or su==sv:return su or sv
 d0=u[0]**2+3*u[1]**2-2*(v[0]**2+3*v[1]**2)
 d1=2*u[0]*u[1]-4*v[0]*v[1]
 return su*sg(d0,d1)
for (k,a),(l,b) in combinations(W57,2):
 ords=[i for i in range(3) if rad57[k][i]*rad57[l][i]]
 if not ords: continue
 cs=[c57(a[i]-b[i]) for i in ords]
 assert all(c is not None for c in cs)
 if k==l:
  z=(F(-1,2),0,0,0)
  for i,c in zip(ords,cs):z=add4(z,scl(c,rad57[k][i]))
  assert sgn4(z)<=0
 else:
  w={rad57[k][i]*rad57[l][i] for i in ords}
  assert len(w)==1
  z=(0,0,0,0)
  for c in cs:z=add4(z,c)
  assert sgn4(z)<=0 or sgn4(add4(scl(mul4(z,z),next(iter(w))),(F(-1,4),0,0,0)))<=0
print('Independent 57-point witness: 1596 exact pair inequalities')
