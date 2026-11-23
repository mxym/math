"""Exact short-vector census for the simultaneous Hoffman / 33-set residual dual.
Uses only the standard library. No solver, symmetry assumption, or remote data.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt

def raw(a,t,d,s,D):
 if a<0:a,d,s=-a,-d,-s
 if t<11*abs(a) or (t-a)%2 or a==0 and 0<t<18 or a==1 and t<=19:return False
 if (a,t)in [(0,14),(0,16),(0,20),(0,26),(1,21),(1,25),(2,24),(2,26),(2,28),(2,30),(3,37)]:return False
 if (a,t)==(0,0):return(d,s)==(0,0)
 if(a,t)==(2,22):return(d,s)==(22,D)
 return True
def star(D):
 l=3*D-22;det=154*22-l*l;U=F(22,7);V=F(22,9);UV=F(l,21)
 bs=set(); survived=[]
 for a in range(5):
  for t in range(51):
   if F(t,7)-F(11*a*a,63)>F(23,10)+(U+V+2*abs(UV))/4:continue
   for p in range(-isqrt(22*t),isqrt(22*t)+1):
    if (p-4*a)%7:continue
    for s in range(-isqrt(33*t),isqrt(33*t)+1):
     if (t-2*a*a-(s-6*a)**2)%7 not in [0,1,2,4]:continue
     a0=F(11*a,3)-s;b0=F(22*a,21)-F(3*p,7)
     i0=F(7,det)*(22*a0-l*b0);j0=F(3,det)*(154*b0-l*a0)
     if 2*max(abs(i0),abs(j0))>1:continue
     zz=F(t,7)-F(11*a*a,63) -(22*a0*a0-2*l*a0*b0+154*b0*b0)/det
     if zz>F(23,10) or zz<0:continue
     def move(i,j):
      aaa=a+2*i+3*j;tt=t+22*i*i+33*j*j+2*D*i*j+2*i*p+2*j*s;pp=p+22*i+D*j;ss=s+D*i+33*j;k=(aaa+4)//9
      return aaa-9*k,tt-22*aaa*k+99*k*k,pp-22*k,ss-33*k
     if all(raw(*move(i,j),D)for i,j in product(range(-3,4),repeat=2)):
      survived.append((a,t,p,s,zz))
 expected=[(0,0,0,0,F(0)),(0,18,0,-9,F(108,53)if D==5 else F(153,76)),(0,18,0,9,F(108,53)if D==5 else F(153,76))]
 assert sorted(survived)==expected, (D,survived)
 print('overlap',D,': centered signatures through 23/10:',expected)
star(5);star(12)
