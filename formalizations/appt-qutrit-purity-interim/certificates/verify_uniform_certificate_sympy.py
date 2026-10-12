"""Independent exact symbolic verifier for the all-large-dimension certificate.
No imports from finder, no optimization, no floating-point operations.
"""
import sympy as s,json,ast,re,time
from pathlib import Path
root=Path(__file__).parent;j=json.loads((root/'qutrit_uniform_parameter_search.json').read_text());assert j['exact_certificate']
g=s.symbols('g1:10');t,z=s.symbols('t z');xs=(*g,t,z);w=t+z-18
y=[sum(g[i:]) for i in range(9)]
A=s.Matrix([[2*y[8],y[7]-y[0],y[5]-y[1]],[y[7]-y[0],2*y[6],y[4]-y[2]],[y[5]-y[1],y[4]-y[2],2*y[3]]])
B=s.Matrix([[2*y[8],y[7]-y[0],y[6]-y[1]],[y[7]-y[0],2*y[5],y[4]-y[2]],[y[6]-y[1],y[4]-y[2],2*y[3]]])
a,b=y[2],y[3];T=sum(y)+t*a+z*b;D=9+t+z;S=sum(v*v for v in y)+t*a*a+z*b*b
core=t*a-z*b;score=9*T-4*D*(a+b)
cache={};coeff={}
def base_expr(name):
 if name in cache:return cache[name]
 if name.startswith('gprod'):p=s.prod(g[i] for i in ast.literal_eval(name[5:]))
 elif name.startswith('ratio'):
  m=re.fullmatch(r'ratio\*g(\d+)g(\d+)',name);assert m
  p=(2*b-a)*g[int(m[1])-1]*g[int(m[2])-1]
 else:
  M={'A':A,'B':B}[name[0]];tail=name[1:]
  if tail=='det':p=M.det()
  elif (m:=re.fullmatch(r'minor(\d)(\d)\*g(\d+)',tail)):
   u,v,k=map(int,m.groups());p=(M[u,u]*M[v,v]-M[u,v]**2)*g[k-1]
  else:
   m=re.fullmatch(r'quad(\([^)]*\))\*g(\d+)g(\d+)',tail);assert m,name
   v=s.Matrix(ast.literal_eval(m[1]));p=(v.T*M*v)[0]*g[int(m[2])-1]*g[int(m[3])-1]
 cache[name]=p;return p
start=time.time()
for num,e in enumerate(j['terms']):
 c=s.Rational(e['coefficient']);assert c>0,name if 'name' in locals() else ''
 name=e['name']
 if name.startswith('plain:'):
  m=tuple(map(int,name[6:].split(',')));coeff[m]=coeff.get(m,0)+c;continue
 if '*param' in name:
  bn,pn=name.rsplit('*param',1);p=base_expr(bn)*s.prod([t,z,w][i] for i in ast.literal_eval(pn))
 elif name.startswith('mixedSquare'):
  m=re.fullmatch(r'mixedSquare\*g(\d+)\*(1|t|z|w)',name);assert m
  p=core**2*g[int(m[1])-1]*{'1':1,'t':t,'z':z,'w':w}[m[2]]
 else:
  m=re.fullmatch(r'scoreSquare(-?\d+),(-?\d+)\*g(\d+)\*(1|t|z|w)',name);assert m,name
  c0,c1,gi=map(int,m.groups()[:3]);p=(c0*score+c1*core)**2*g[gi-1]*{'1':1,'t':t,'z':z,'w':w}[m[4]]
 for m,v in s.Poly(s.expand(p),xs).terms():coeff[m]=coeff.get(m,0)+c*v
 if num%100==0:print('checked',num,flush=True)
expected=dict(s.Poly(s.expand((9*T*T-8*D*S)*T),xs).terms())
assert {m:v for m,v in coeff.items() if v}==expected
print('PASS independent exact uniform identity; all',len(j['terms']),'coefficients positive; seconds',time.time()-start,flush=True)
