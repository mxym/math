#!/usr/bin/env python3
"""Exact auxiliary obstruction certificate; not a main counterexample."""
from fractions import Fraction as F
from math import comb
import json
import sys
from pathlib import Path
if not __debug__:
 print("Verification requires enabled assertions; run ordinary Python 3.", file=sys.stderr)
 raise SystemExit(2)
c=[1,9,28,48,49,27,8,1]
G=[F((-1)**(7-j)*c[7-j]) for j in range(8)] # ascending

def trim(a):
 while len(a)>1 and not a[-1]:a.pop()
 return a

def rem(a,b):
 a=trim(a[:]);b=trim(b[:])
 while len(a)>=len(b) and any(a):
  v=a[-1]/b[-1];r=len(a)-len(b)
  for j,z in enumerate(b):a[j+r]-=v*z
  trim(a)
 return a

def mul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return trim(r)

def finite_rem(a,b,q):
 a=[int(v)%q for v in a];b=[int(v)%q for v in b];trim(a);trim(b)
 while len(a)>=len(b) and any(a):
  v=a[-1]*pow(b[-1],-1,q)%q;r=len(a)-len(b)
  for j,z in enumerate(b):a[j+r]=(a[j+r]-v*z)%q
  trim(a)
 return a

def finite_pow(a,n,b,q):
 r=[1]
 while n:
  if n&1:r=finite_rem(mul(r,a),b,q)
  a=finite_rem(mul(a,a),b,q);n//=2
 return r

def gcd(a,b,q):
 while any(b):a,b=b,finite_rem(a,b,q)
 return a
q=11
A=[int(v)%q for v in G]
r=finite_pow([0,1],q,A,q);r += [0]*(2-len(r));r[1]=(r[1]-1)%q
assert len(gcd(A,trim(r),q))==1
assert finite_pow([0,1],q**7,A,q)==[0,1]

def det(a):
 a=[r[:] for r in a];n=len(a);prev=1;sign=1
 for k in range(n-1):
  if not a[k][k]:
   r=next(r for r in range(k+1,n) if a[r][k]);a[k],a[r]=a[r],a[k];sign=-sign
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    z=a[i][j]*pivot-a[i][k]*a[k][j]
    assert z%prev==0;a[i][j]=z//prev
  for i in range(k+1,n):a[i][k]=0
  prev=pivot
 return sign*a[-1][-1]
P=[int(v) for v in G[::-1]];D=[(7-i)*v for i,v in enumerate(P[:-1])]
Syl=[]
for i in range(6):Syl.append([0]*i+P+[0]*(5-i))
for i in range(7):Syl.append([0]*i+D+[0]*(6-i))
Discriminant=-det(Syl)
assert Discriminant==93667157
sturm=[G,[F(j)*G[j] for j in range(1,len(G))]]
while any(sturm[-1]):
 r=rem(sturm[-2],sturm[-1]);
 if not any(r):break
 sturm.append([-v for v in r])
def changes(v):
 v=[1 if z>0 else -1 for z in v if z]
 return sum(a!=b for a,b in zip(v,v[1:]))
real_count=changes([p[-1]*(-1)**(len(p)-1) for p in sturm])-changes([p[-1] for p in sturm])
positive_count=changes([p[0] for p in sturm])-changes([p[-1] for p in sturm])
assert real_count==positive_count==3
slacks=[c[k]**2*comb(7,k-1)*comb(7,k+1)-c[k-1]*c[k+1]*comb(7,k)**2 for k in range(1,7)]
assert slacks==[329,1568,12740,177135,5733,21]
assert all(z>0 for z in slacks)
assert all(c[k]>=comb(7,k) for k in range(8))
assert sum(comb(a,k) for a,k in [(7,4),(5,3),(3,2),(1,1)])==49
shadow=sum(comb(a,k-1) for a,k in [(7,4),(5,3),(3,2),(1,1)])
assert shadow==49>c[3]
# Formal numerator identity for every integer a,b, not a finite sample.
assert [7*25,7*18,7*7]==[9**2+94,2*7*9,7**2]
p=[7]
for k in range(1,5):
 v=sum((-1)**(j-1)*c[j]*p[k-j] for j in range(1,k+1))-(-1)**(k-1)*c[k]*(7-k)
 p.append(v)
H3=det([[p[i+j] for j in range(3)] for i in range(3)])
assert H3==-3432
assert p[:3]==[7,9,25]
# Retaining the actual norm magnitude rules out this candidate.
affine_a,affine_b=1,-3
square_trace=affine_a**2*p[2]+2*affine_a*affine_b*p[1]+affine_b**2*p[0]
g_at_3=sum(int(v)*3**j for j,v in enumerate(G))
affine_norm=(-1)**7*g_at_3
left=square_trace**7
right=7**7*affine_norm**2
assert g_at_3==-355 and affine_norm==355 and square_trace==34
assert left==52523350144 and right==103787006575 and left<right
out={'scope':'auxiliary relaxation obstruction; NOT Bell-Skandera counterexample','coefficients':c,'irreducible_mod_prime':q,'discriminant':Discriminant,'strict_Newton_slacks':slacks,'real_roots':real_count,'positive_reciprocal_roots':positive_count,'uniform_affine_square_trace_bound':{'bound':7,'domain':'all nonzero integer pairs (a,b)','uses_only_norm_absolute_value_at_least':1,'proof':'completed square identity and integer case split'},'strong_actual_norm_negative_certificate':{'affine_pair':[affine_a,affine_b],'square_trace':square_trace,'absolute_norm':abs(affine_norm),'trace_power_7':left,'seven_power_7_times_norm_squared':right,'actual_norm_AM_GM_inequality_holds':False},'KK_failure':{'k':4,'shadow':shadow,'previous':c[3]},'Hermite_3_determinant':H3}
print(json.dumps(out,indent=2))
Path(__file__).with_name('arithmetic_relaxation_exact.json').write_text(json.dumps(out,indent=2)+'\n')
