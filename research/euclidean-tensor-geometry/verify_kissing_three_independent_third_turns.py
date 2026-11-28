#!/usr/bin/env python3
"""Exact root and non-root witnesses for three independent third turns."""
if not __debug__:
    raise RuntimeError("Re-run normal Python without -O or -OO; the verifier uses assertions.")
from itertools import product,combinations
# Work in Z[omega]^3 with omega^2+omega+1=0 and real scaling 1/sqrt(3).
O=((1,0),(0,1),(-1,-1))
def mo(p):a,b=p;return -b,a-b
def neg(x):return tuple(-z for z in x)
def cp(x,y):return tuple(a+b for a,b in zip(x,y))
x=(2,1);ax=[]
for i in range(3):
 ax.append(x);x=mo(x)
T={tuple(z for u in p for z in u)for p in product(O,repeat=3)}
X=T|{neg(x)for x in T}
for j in range(3):
 for u in ax:
  p=(0,0)*j+u+(0,0)*(2-j);X.add(p);X.add(neg(p))
def gram(x,y):
 q=sum(2*a*c-a*d-b*c+2*b*d for a,b,c,d in zip(x[::2],x[1::2],y[::2],y[1::2]));assert q%3==0;return q//3
assert len(X)==72 and all(gram(x,x)==2 for x in X)
assert all(gram(x,y)in(-2,-1,0,1)for x,y in combinations(X,2))
def pos(x):return sum(v*11**i for i,v in enumerate(x))>0
XP={x for x in X if pos(x)}
assert len(XP)==36
S=sorted(XP-{cp(a,b)for a in XP for b in XP})
assert len(S)==6
G=[[gram(x,y)for y in S]for x in S];es=[(i,j)for i,j in combinations(range(6),2)if G[i][j]==-1]
assert all(G[i][j]in(-1,0)for i,j in combinations(range(6),2))and len(es)==5
graph=[{j for j in range(6)if G[i][j]==-1}for i in range(6)]
c=next(i for i in range(6)if len(graph[i])==3)
def arm(p,t):
 v=1
 while graph[t]-{p}:
  assert len(graph[t]-{p})==1;p,t=t,next(iter(graph[t]-{p}));v+=1
 return v
assert sorted(arm(c,j)for j in graph[c])==[1,2,2]
q={S[0]}
while not all(tuple(v-gram(a,b)*w for v,w in zip(a,b))in q for a in q for b in S):q|={tuple(v-gram(a,b)*w for v,w in zip(a,b))for a in q for b in S}
assert q==X
print('E6 certificate',len(X),'roots, simple edges',es,'arms 1,2,2 and Weyl orbit',len(q))

def gen(z,j):
 for _ in range(j):z=mo(z)
 return z
def signed_orbit(u):
 out=set()
 for g in product(range(3),repeat=3):
  p=tuple(e for j,t in enumerate(g)for e in gen(u[j],t));out.add(p);out.add(neg(p))
 return out
B=signed_orbit(((3,0),(0,0),(0,0)))|signed_orbit(((2,1),(2,0),(0,0)))|signed_orbit(((2,1),(0,0),(2,0)))|signed_orbit(((0,0),(2,1),(2,1)))
def d36(x,y):
 return sum(w*(2*a*c-a*d-b*c+2*b*d)for a,b,c,d,w in zip(x[::2],x[1::2],y[::2],y[1::2],(2,3,3)))
assert len(B)==60 and {d36(x,x)for x in B}=={36}
wvals={d36(x,y) for x,y in combinations(B,2)}
assert max(wvals)==18 and 12 in wvals
print("non-E6 extremum",len(B),"points; exact off-diagonal products times 36",sorted(wvals))
# Symbolic sign margins for the phase bounds in the proof:
# sqrt(5)>11/5 makes cos36>4/5; 1/sqrt2>7/10. Also
# sqrt(5)<7/3 makes sin36>1/sqrt3, and sqrt(5)>2.
from fractions import Fraction as F
assert F(11,5)**2<5<F(7,3)**2 and F(7,10)**2<F(1,2)
assert 2*9>16 and 8>F(27,4) and 5>4

# All 57 points for the exactly-one-triple stratum. Encode a phase by
# 15-degree units; inactive coordinates use None. Within each seed all active
# radii are 1/sqrt(support size). 4*cos(j*pi/12) in basis 1,sqrt2,sqrt3,sqrt6.
from math import isqrt
cos_table=((4,0,0,0),(0,1,0,1),(0,0,2,0),(0,2,0,0),(2,0,0,0),
           (0,-1,0,1),(0,0,0,0))
def c4(j):
 j=j%24
 if j>12:j=24-j
 return cos_table[j] if j<=6 else neg(cos_table[12-j])
def pos_surds(v):
 if not any(v):return 0
 scale=10**6
 lo=hi=0
 for a,d in zip(v,(1,2,3,6)):
  n=d*scale**2;l=isqrt(n);u=l+(l*l<n)
  lo+=min(a*l,a*u);hi+=max(a*l,a*u)
 assert lo>0 or hi<0
 return 1 if lo>0 else -1
def phase_seed(v):
 return {tuple((a+8*g[i])%24 if a is not None else None for i,a in enumerate(v))for g in product(range(3),repeat=3)}
W=set().union(*(phase_seed(v)for v in [(0,0,0),(2,None,None),(5,4,None),(5,None,4),(None,4,4)]))
assert len(W)==57
sq={1:(1,0,0,0),2:(0,1,0,0),3:(0,0,1,0),4:(2,0,0,0),6:(0,0,0,1),9:(3,0,0,0)}
num=0
for x,y in combinations(W,2):
 k=sum(a is not None for a in x)*sum(b is not None for b in y)
 v=tuple(-2*z for z in sq[k])
 for a,b in zip(x,y):
  if a is not None and b is not None:v=cp(v,c4(a-b))
 assert pos_surds(v)<=0
 num+=1
assert num==1596
# Margin certificates at the two symmetry classes of triangle vertices.
assert 4*4<9*3 and 25<27
print('one-triple extremum',len(W),'points;',num,'off-diagonal tests in Q(sqrt(2),sqrt(3))')
