#!/usr/bin/env python3
"""Direct equality check on every unrounded output of the two implementations (SymPy required)."""
import verify as V, symbolic as S
import sympy as s
P=sorted(V.table()[1])
def sy(A):
 c,k,p=A
 if k==2:return S.full(c,*map(s.Rational,p))
 if k==1:
  x,y,h=map(s.Rational,p);return (c,s.Matrix([y,-x]),s.diag(h,0) if x else s.diag(0,h))
 return (c,s.eye(2),s.zeros(2))
def eq(A,B):
 if S.encode(*sy(A))!=S.encode(*B):raise ArithmeticError((A,B))
z=0
for a,b in V.product(P,repeat=2):
 for series in (True,False):
  eq(V.combine(a,b,series),S.get(sy(a),sy(b),'S' if series else 'P'));z+=1
for a,j,i in V.product(P,range(4),range(2)):
 eq(V.decoration(a,j,i),S.get(sy(a),(j,i),'D'));z+=1
for a in P:eq(V.close(a),S.get(sy(a),None,'F'));z+=1
print('PASS raw emitted costs, domains and form on the whole domain match between the authors’ scalar and symbolic implementations for all',z,'operations')
