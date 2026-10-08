#!/usr/bin/env python3
"""Additional independent checks for the general construction. No floats."""
from fractions import Fraction as F
from itertools import permutations
from functools import reduce
from operator import mul
from pathlib import Path
import json

def inv(p): return sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
checks=[]
for n in range(4,9):
    a,b,c=F(-4,5),F(1,17),F(1,13)
    A=[[F(int(i==j)) for j in range(n)] for i in range(n)]
    for i,j,v in [(0,1,a),(0,n-1,b),(1,n-1,c)]: A[i][j]=A[j][i]=v
    got={}
    for p in permutations(range(n)):
        v=reduce(mul,(A[i][p[i]] for i in range(n)),F(1))
        if v: got[inv(p)]=got.get(inv(p),F(0))+v
    m=2*n-5
    assert got=={0:F(1),1:a*a,m:c*c,m+1:2*a*b*c,m+2:b*b}
    checks.append(n)

# Exact checks of the radical construction without approximating radicals:
# a^2=s, c^2=u, b=-a*k*c, so b^2=s*k^2*u and abc=-s*k*u.
family=[]
for t in [F(2),F(3,2),F(11,10)]:
    m=3
    while t**(m-1)<=32*(m+1)**2*(m+2): m+=2
    delta=F(1,2*(m+1)**2)
    s=1-delta; u=delta/8; k=F(m+1,m+2)/t
    det=1-s-u-s*k*k*u-2*s*k*u
    direct_derivative=s+m*u*t**(m-1)-2*(m+1)*s*k*u*t**m+(m+2)*s*k*k*u*t**(m+1)
    claimed=1-delta-t**(m-1)/F(32*(m+1)**2*(m+2))
    assert det>delta/2>0
    assert direct_derivative==claimed < -delta < 0
    family.append({'t':str(t),'m':m,'n':(m+5)//2,'delta':str(delta),'determinant':str(det),'derivative':str(direct_derivative),'exact_assertions':'PASS'})

# Explicit all-nonzero rational variant, useful if irreducibility is desired.
A=[[F(1), F(-99,100),F(1,10000),F(1,500)],[F(-99,100),F(1),F(1,10000),F(1,8)],[F(1,10000),F(1,10000),F(1),F(1,10000)],[F(1,500),F(1,8),F(1,10000),F(1)]]
det=lambda B:sum((-1)**inv(p)*reduce(mul,(B[i][p[i]] for i in range(len(B))),F(1)) for p in permutations(range(len(B))))
minors=[det([r[:k] for r in A[:k]]) for k in range(1,5)]
derivative=sum(inv(p)*50**(inv(p)-1)*reduce(mul,(A[i][p[i]] for i in range(4)),F(1)) for p in permutations(range(4)) if inv(p))
assert all(d>0 for d in minors)
assert derivative==F(-2707509509,625000000)<0
r={'status':'PASS','full_enumeration_spaced_triangle_orders':checks,'family_exact_test_instances':family,'all_nonzero_variant':{'matrix':[[str(x) for x in r] for r in A],'leading_minors':[str(x) for x in minors],'Pprime(50)':str(derivative)},'warning':'Finite checks supplement the symbolic proof; they do not prove the universal quantifiers.'}
Path(__file__).with_name('family_results.json').write_text(json.dumps(r,indent=2)+'\n')
print('PASS: full permutation enumeration n=4,...,8; exact radical-family tests:', [(i['t'],i['m'],i['n']) for i in family], '; dense variant verified.')
