"""Alternative FEI replay from Numaro's historical artifact, not the graph table.

Usage: python3 -B crosscheck.py /path/to/fei_c71_n18_artifact.json
The Walsh transforms, influences and endpoint comparisons use exact arithmetic.
Decimal entropy values provide corroboration, not a second interval proof.
"""
import sys
from pathlib import Path
from fractions import Fraction as Q
from decimal import Decimal as D, getcontext
import json, hashlib
def check(condition, label):
 if not condition: raise ArithmeticError(label)
getcontext().prec=75
def dec(x):return D(x.numerator)/D(x.denominator)
def eta(p):return -dec(p)*dec(p).ln()/D(2).ln() if p else D(0)
def fw(v):
 v=v[:]; l=1
 while l<len(v):
  for b in range(0,len(v),2*l):
   for j in range(b,b+l): v[j],v[j+l]=v[j]+v[j+l],v[j]-v[j+l]
  l*=2
 return v
if len(sys.argv)!=2:
 raise SystemExit(__doc__)
d=json.loads(Path(sys.argv[1]).read_text())
raw=int(d['true_hex'],16).to_bytes(1<<15,'little')
table=[1-2*((b>>i)&1) for b in raw for i in range(8)]
expected='f8a7bb2c738d86368305111633376b1a3a83d8ee1f1abcc9a37d841b0f9c7839'
check(hashlib.sha256(','.join(map(str,table)).encode()).hexdigest()==expected==d['sha256_table'], 'historical truth table hash')
# Core read directly as sections of the public n=18 truth table; no K3,3 graph,
# no guessed chart/order arrays and no orbit tables in the reconstruction.
charts={}; u=[]; v=[0]*512
for x in range(512):
 vals=tuple(table[x::512]);u.append(sum(vals)//512)
 if not u[-1]:
  j,= [j for j in range(9) if vals[1<<j]!=vals[0]]
  check(all(z==1-2*((i>>j)&1) for i,z in enumerate(vals)),'private selector')
  charts.setdefault(j,[]).append(x)
check(len(charts)==9, 'nine charts')
for j,(a,b) in charts.items():
 c=a^b; check(c.bit_count()==1,'one free core bit');v[a]=1 if not a&c else -1;v[b]=-v[a]
A=[Q(a,512) for a in fw(u)];V=[Q(a,512) for a in fw(v)]
mass=lambda w: sum(w)
weights=[i.bit_count() for i in range(512)]
J=lambda w:sum(wi*ci for wi,ci in zip(w,weights))
for label,metric in [('Parseval mass polynomial',mass),('spectral first moment polynomial',J)]:
 print(label,tuple(metric([f(a,b) for a,b in zip(A,V)]) for f in [lambda a,b:a*a, lambda a,b:2*a*b, lambda a,b:b*b]))
check((J([a*a for a in A]),J([2*a*b for a,b in zip(A,V)]),J([b*b for b in V]))==(Q(477,256),0,Q(45,256)), 'independent influence coefficients')
# Exact transform of ALL n=18 truth table Fourier coefficients (not an orbit-table reconstruction)
F=fw(table);den=1<<18;h=Q(1,256)
from collections import Counter
hcounts=Counter(map(abs,F))
H=sum(m*eta(Q(x*x,den**2)) for x,m in hcounts.items())
I=sum(Q(f*f*i.bit_count(),den**2) for i,f in enumerate(F))
prob=Q(F[1],den);N=18
print('B',N,I,prob,H/dec(I-1))
# Derive mixed graft entropy by core Walsh arrays + literal 256-copy reweighting:
# Entropy of nonempty-private labels after reweighting p->h^2 p on 256 copies.
for epoch in [1,2]:
 inner_H=H;inner_I=I; t=prob
 for _ in range(3):
  inner_H=H+dec(prob)*inner_H
  inner_I=I+prob*(inner_I-1)
  t*=prob
 p=[(a+t*b)**2 for a,b in zip(A,V)]
 H=sum(count*eta(w) for w,count in Counter(p).items()) + D(9*256)*(dec(h*h)*(inner_H-eta(t*t))+dec(1-t*t)*eta(h*h))
 I=J(p)+9*h*(inner_I-t*t+4*(1-t*t))
 prob=A[1]+t*V[1]; N=9*(4*N-3)
 print('E',N,I,prob,H/dec(I-1))
# Rational check: an actual finite composition clears the quoted thresholds,
# using the lower interval established separately by the original checker.
L=Q('6.5218511567353856')
check(L*(1-I**(-20)) > Q('6.5218457109230466'), 'depth 20')
check(L*(1-I**(-48)) > Q('6.52185115673538'), 'depth 48')
