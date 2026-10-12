"""Independent exact check: Python Fraction and sparse polynomial dictionaries.
No SymPy, SciPy, optimizer, floating-point arithmetic, or imported search code.
"""
from fractions import Fraction as F
from pathlib import Path
import json,re,ast,itertools
N=9; ZERO=(0,)*N
def const(c):return {ZERO:F(c)} if c else {}
def var(i):
 e=list(ZERO);e[i]=1;return {tuple(e):F(1)}
def add(*ps):
 out={}
 for p in ps:
  for m,c in p.items():out[m]=out.get(m,F(0))+c
 return {m:c for m,c in out.items() if c}
def scale(c,p):return {m:F(c)*a for m,a in p.items() if c*a}
def mul(p,q):
 out={}
 for a,c in p.items():
  for b,d in q.items():
   m=tuple(x+y for x,y in zip(a,b));out[m]=out.get(m,F(0))+c*d
 return {m:c for m,c in out.items() if c}
def sub(p,q):return add(p,scale(-1,q))
def det(M):
 out={}
 for p in itertools.permutations(range(3)):
  term=const((-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3)))
  for i in range(3):term=mul(term,M[i][p[i]])
  out=add(out,term)
 return out
g=[var(i) for i in range(N)];a=[add(*g[i:]) for i in range(N)]
A=[[scale(2,a[8]),sub(a[7],a[0]),sub(a[5],a[1])],
   [sub(a[7],a[0]),scale(2,a[6]),sub(a[4],a[2])],
   [sub(a[5],a[1]),sub(a[4],a[2]),scale(2,a[3])]]
B=[[scale(2,a[8]),sub(a[7],a[0]),sub(a[6],a[1])],
   [sub(a[7],a[0]),scale(2,a[5]),sub(a[4],a[2])],
   [sub(a[6],a[1]),sub(a[4],a[2]),scale(2,a[3])]]
def term(name):
 if name.startswith('gprod'):
  out=const(1)
  for i in ast.literal_eval(name[5:]):out=mul(out,g[i])
  return out
 M={'A':A,'B':B}[name[0]];tail=name[1:]
 if tail=='det':return det(M)
 m=re.fullmatch(r'minor(\d)(\d)\*g(\d)',tail)
 if m:
  i,j,k=map(int,m.groups())
  return mul(sub(mul(M[i][i],M[j][j]),mul(M[i][j],M[i][j])),g[k-1])
 m=re.fullmatch(r'quad(\([^)]*\))\*g(\d)g(\d)',tail)
 assert m,name
 v=ast.literal_eval(m[1]);i,j=int(m[2])-1,int(m[3])-1
 q=add(*(scale(v[x]*v[y],M[x][y]) for x in range(3) for y in range(3)))
 return mul(mul(q,g[i]),g[j])
j=json.loads(Path(__file__).with_name('qutrit_cubic_certificate_search.json').read_text())
assert j['exact_certificate']
assert all(F(t['coefficient'])>0 for t in j['terms'])
rhs=add(*(scale(F(t['coefficient']),term(t['name'])) for t in j['terms']))
T=add(*a);lhs=mul(sub(scale(17,mul(T,T)),scale(121,add(*(mul(x,x) for x in a)))),T)
assert sub(lhs,rhs)=={},'NONZERO EXACT RESIDUAL'
print('PASS: exact degree-three identity; all',len(j['terms']),'coefficients strictly positive; no float used')
print('Each generator is nonnegative for nonnegative gaps and PSD A,B.')
