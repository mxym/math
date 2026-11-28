#!/usr/bin/env python3
"""Exact certificate for the four-gate support classification and forest law.
Uses only the Python standard library. Site labels in the data are 1-based.
"""
from itertools import combinations,permutations,product
E=list(combinations(range(4),2))
P=list(permutations(range(4)))
def orbit(w):
 W={w}; todo=[w]
 while todo:
  x=todo.pop()
  y=[x[::-1]]+[tuple(tuple(sorted((p[u],p[v]))) for u,v in x) for p in P]
  y += [x[:i]+(x[i+1],x[i])+x[i+2:] for i in range(3) if not set(x[i])&set(x[i+1])]
  for z in y:
   if z not in W:W.add(z);todo.append(z)
 return W
def forest(B):
 cl=list(range(4+len(B)))
 def root(x):
  while x!=cl[x]:x=cl[x]
  return x
 for k,bb in enumerate(B,4):
  for i in sorted(bb):
   a,b=root(k),root(i)
   if a==b:return False
   cl[a]=b
 return True
def check(w):
 for mask in range(8):
  k=[0]+[i+1 for i in range(3) if mask>>i&1]+[4]
  Q=[set(t for e in w[a:b] for t in e) for a,b in zip(k,k[1:])]
  if max(map(len,Q))<=3 and forest(Q):return Q
def classes():
 D={}; covered=set()
 for w in product(E,repeat=4):
  if w in covered: continue
  o=orbit(w); assert not (o & covered); covered |= o
  W=[(a,check(a)) for a in sorted(o) if check(a)]
  D[w]=(len(o),W[0] if W else None)
 assert len(covered)==1296
 return D

from fractions import Fraction as F
from math import prod

# Input order is chronological. Ordered pairs are rows I, columns J.
BAD = {
 "12131412": ("AAAA", "12:23 -13:12 14:13 14:14 14:23", -5537109375),
 "12131424": ("AAAA", "-12:34 13:14 14:13 14:14 14:23", -4130859375),
 "12132412": ("AAAA", "12:12 12:14 12:23 13:14 -14:24", -5537109375),
 "12132414": ("AAAB", "12:23 -13:13 14:12 14:14 14:23", -4130859375),
 "12132434": ("AAAA", "-12:12 13:13 13:14 13:24 14:24", -2187500000),
 "12133424": ("AAAB", "-12:12 13:14 14:14 14:23 14:24", -2187500000),
 "12341324": ("AACD", "-12:23 13:12 13:13 13:34 14:12", -3076555218750),
}
ANGLES = dict(A=(3,4,5), B=(4,3,5), C=(5,12,13), D=(12,5,13))

def edge(s):
 return tuple(int(c)-1 for c in s)
def key(w):
 return ''.join(str(i+1)+str(j+1) for i,j in w)
def idm(n):
 return [[int(i==j) for j in range(n)] for i in range(n)]
def mul(A,B):
 return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def givens(n,e,c,s,d):
 i,j=e
 M=[[d*x for x in row] for row in idm(n)]
 M[i][i]=M[j][j]=c
 M[i][j],M[j][i]=s,-s
 return M
def det(U,I,J):
 def parity(p):
  return (-1)**sum(x>y for x,y in combinations(p,2))
 return sum(parity(p)*prod(U[i][J[p[t]]] for t,i in enumerate(I))
            for p in permutations(range(len(I))))
def check_bad(w,desc):
 angles,L,expected=desc
 U=idm(4);d=1
 for e,h in zip(w,angles):
  c,s,q=ANGLES[h]
  U=mul(givens(4,e,c,s,q),U);d*=q
 assert mul(U,list(zip(*U)))==[[d*d*x for x in row] for row in idm(4)]
 terms=[]
 for token in L.split():
  i,j=token.lstrip('-').split(':')
  terms.append((frozenset(edge(i)),tuple(edge(j)),-1 if token[0]=='-' else 1))
 values=[sum(s for i,j,s in terms if frozenset(p[t] for t in j)==i) for p in P]
 assert set(values)=={0,1,2}
 z=sum(s*det(U,tuple(sorted(i)),j)**2 for i,j,s in terms)
 assert z==expected<0
 print(key(w),angles,'negative numerator',z,'denominator',d**4)

def birkhoff_3(block,n,U):
 # Expect identity on modes outside this block. Exact Birkhoff greedy.
 ps=list(permutations(block))
 A={(i,j):U[i][j]**2 for i in block for j in block}
 mu=[]
 while sum(A.values()):
  p=next(p for p in ps if all(A[i,j]>0 for i,j in zip(p,block)))
  t=min(A[i,j] for i,j in zip(p,block))
  q=list(range(n))
  for i,j in zip(p,block):A[i,j]-=t;q[j]=i
  mu.append((tuple(q),t))
 assert sum(t for q,t in mu)==1
 return mu
def test_circuit_all_orders():
 from random import Random
 R=Random(90210)
 B=[(0,1,2),(1,3,4),(0,),(4,5),(4,6)]
 n=7
 U=[];W=[]
 for J in B:
  a=idm(n)
  for i,j in combinations(J,2):
   c,s,d=R.choice(list(ANGLES.values()))
   a=mul([[F(x,d) for x in row] for row in givens(n,(i,j),c,s,d)],a)
  U.append(a);W.append(birkhoff_3(J,n,a))
 assert forest_on(B,n)
 trials=0
 for order in [(0,1,2,3,4),(1,4,2,3,0),(4,3,0,2,1)]:
  V=idm(n);law={tuple(range(n)):F(1)}
  for k in order:
   V=mul(U[k],V);curr={}
   for p,a in law.items():
    for q,b in W[k]:
     r=tuple(q[i] for i in p);curr[r]=curr.get(r,F(0))+a*b
   law=curr
  assert sum(law.values())==1
  for k in range(n+1):
   T=list(combinations(range(n),k))
   # Determinant permutations at orders 5,6,7 add no independent information.
   if k>=5:continue
   for J in T:
    H={}
    for p,b in law.items():
     I=tuple(sorted(p[i] for i in J));H[I]=H.get(I,F(0))+b
    for I in T:
     assert det(V,I,J)**2==H.get(I,F(0))
     trials+=1
 print('all-path rational controls',trials)
def forest_on(B,n):
 edges=sum(map(len,B))
 cs=[{i} for i in range(n+len(B))]
 for k,b in enumerate(B,n):
  for i in b:
   ci=next(s for s in cs if i in s)
   ck=next(s for s in cs if k in s)
   if ci is ck:return False
   cs.remove(ci);cs.remove(ck);cs.append(ci|ck)
 return len(cs)==n+len(B)-edges

def main():
 C=classes()
 bad={key(w) for w,(n,b) in C.items() if b is None}
 assert len(C)==31 and bad==set(BAD) and sum(n for n,b in C.values() if b is not None)==1080
 for w,(n,b) in C.items():
  if b is None:check_bad(w,BAD[key(w)])
 print('ordered words: 1080 universally inside the minors polytope, 216 not universal')
 test_circuit_all_orders()
 print('PASS')

if __name__=='__main__':
 main()
