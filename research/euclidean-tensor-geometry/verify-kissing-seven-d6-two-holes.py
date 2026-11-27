#!/usr/bin/env python3
"""Exact acute two-hole polar and D6 reflection-generation checks."""
from itertools import combinations,product
from fractions import Fraction as Q
if not __debug__:raise RuntimeError("enable assertions")
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def solve(A,b):
 T=[[Q(x)for x in row]+[Q(z)]for row,z in zip(A,b)];n=len(T)
 for j in range(n):
  v=next((i for i in range(j,n)if T[i][j]),None)
  if v is None:return None
  T[v],T[j]=T[j],T[v];z=T[j][j];T[j]=[a/z for a in T[j]]
  for i in range(n):
   if i!=j:
    z=T[i][j];T[i]=[a-z*b for a,b in zip(T[i],T[j])]
 return tuple(row[-1] for row in T)
def vs(ineq):
 v=set()
 for rows in combinations(ineq,6):
  q=solve([x for x,_ in rows],[y for _,y in rows])
  if q and all(dot(x,q)<=y for x,y in ineq):v.add(q)
 return v
I=[tuple(int(i==j)for j in range(6))for i in range(6)]
def row(*args):return tuple(sum(s*I[i][j]for s,i in args)for j in range(6))
p=row((1,0),(1,1));q=row((1,0),(1,2));w=tuple(a+b for a,b in zip(p,q));dif=tuple(b-a for a,b in zip(p,q))
pol=[(row((-1,5)),0),(row((-1,4),(1,5)),0),(row((-1,3),(1,4)),0),
     (row((1,0),(1,3)),1),(row((-1,0),(-1,2)),-1),(row((-1,1),(1,2)),0),
     (row((1,1),(1,2)),1)]
lo=vs(pol+[(w,Q(13,5))]);hi=vs(pol+[(tuple(-a for a in w),-Q(13,5))])
assert lo and hi and max(dot(v,v) for v in lo)==Q(3,2)
def dist2(v):
 b=max(0,min(1,dot(tuple(x-y for x,y in zip(v,p)),dif)/dot(dif,dif)))
 return sum((x-y-b*z)**2 for x,y,z in zip(v,p,dif))
assert max(dot(v,v)+3*dist2(v)for v in hi)==2
print("acute joint polar: vertex counts",len(vs(pol)),len(lo),len(hi),"exact maxima 3/2 and 2")
# Reflection in a norm-two root a is v -> v-(v.a)a. Recover any missing lines.
D={row((s,i),(t,j))for i,j in combinations(range(6),2)for s,t in product((-1,1),repeat=2)}
neg=lambda v:tuple(-a for a in v)
def generate(A):
 A=set(A)
 while True:
  v=A|{tuple(x-dot(a,b)*y for x,y in zip(a,b))for a in A for b in A}
  if len(v)==len(A):return v
  A=v
for q in [neg(p),row((1,0),(-1,1)),row((1,2),(1,3)),row((1,0),(1,2)),row((-1,0),(1,2))]:
 assert generate(D-{p,q,neg(p),neg(q)})==D
base={a for a in D if sum(bool(a[2*i] or a[2*i+1])for i in range(3))==2}
assert len(base)==48 and generate(base)==D
print("all applicable projective cores generate all 60 signed D6 roots")
