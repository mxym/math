#!/usr/bin/env python3
"""Exact finite tail of the order-three branch; standard library."""
def fac(n):
 f=[];d=2
 while d*d<=n:
  while n%d==0:f.append(d);n//=d
  d=3 if d==2 else d+2
 if n>1:f.append(n)
 return f
rows=[]
for q in range(3,256,2):
 if fac(q)!=[q]:continue
 for M in set(fac(q*q+1)):
  if M>q and M%q!=1 and pow(M,3,q)==1:
   rows.append((q,M,fac(q**5+M-q)))
if rows!=[(37,137,[23,59,137,373])]:raise ValueError(rows)
if fac(94-7)!=[3,29] or fac(248-3)!=[5,7,7]:raise ValueError('small tails')
print(rows,'PASS')
