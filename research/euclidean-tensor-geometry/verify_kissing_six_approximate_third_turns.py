#!/usr/bin/env python3
"""Exact continuum certificate for relaxed four/three/ternary orbit bounds."""
if not __debug__:raise RuntimeError("Run normal Python without -O.")
from itertools import combinations_with_replacement,product
from fractions import Fraction as Q
from math import isqrt
D=4096;S=10**6
def clo(j):
 if j==D:return S//2
 x=Q(355*j,113*3*D);s=t=Q(1)
 for i in range(1,6):t*=-x*x/((2*i)*(2*i-1));s+=t
 return (s*S).__floor__()
C=[clo(j)for j in range(D+1)];A=[isqrt((74*D+92*j)*S*S//D)for j in range(D+1)];R=isqrt(74*S*S)
def ok(x,w):
 a,l,r=x
 return R*(A[a]*C[l+w]+A[D-a-w]*C[r+w])<=129*S**3
def comp(x,y,w):
 a,l,r=x;b,t,u=y
 return A[a]*A[b]*C[min(D,l+t+2*w,2*D-l-t)]+A[D-a-w]*A[D-b-w]*C[min(D,r+u+2*w,2*D-r-u)]<=129*S**3
w=D//4;B=[v for v in product(range(0,D,w),repeat=3)if ok(v,w)]
p=[(x,y)for x,y in combinations_with_replacement(B,2)if comp(x,y,w)]
hist=[len(p)]
while p and w>1:
 w//=2
 def children(x):return [v for t in product((0,w),repeat=3) if ok((v:=tuple(a+b for a,b in zip(x,t))),w)]
 ch={x:children(x)for q in p for x in q};pp=[]
 for x,y in p:
  pairs=combinations_with_replacement(ch[x],2)if x==y else product(ch[x],ch[y])
  pp.extend((u,v)for u,v in pairs if comp(u,v,w))
 p=pp
 hist.append(len(p))
assert hist==[102,27,38,75,40,36,6,0]
print('Exact relaxed pair-orbit box tree:',hist)
# Radical and trigonometric comparison margins used in the paper.
assert Q(277,5)**2<37*83
r2=Q(37,120);mix=Q(277,5*120);t=Q(43,80)
assert mix+r2/4>t and Q(7,4)*r2>t and Q(7,5)*(r2+mix)>2*t
assert (4*Q(3,4)**3-3*Q(3,4)) < -Q(1,2) and Q(7,8)>Q(9,10)**2
assert Q(3,5)>t and (Q(1,2)+Q(1,41))/(1-Q(1,41))==t
print('Exact phase margins and transfer at epsilon^2 = 1/41 PASS')
