"""Independent symbolic check of recorded certificates; no optimization code."""
import sympy as s,json,ast,re,sys
from pathlib import Path
D=int(sys.argv[1]);root=Path(__file__).parent
path=root/(f'qutrit_D{D}_fast_certificate.json' if D>=15 else (f'qutrit_D{D}_cubic_certificate.json' if D==12 else 'qutrit_cubic_certificate_search.json'))
j=json.loads(path.read_text());assert j['exact_certificate']
g=s.symbols('x0:'+str(D));a=[sum(g[i:]) for i in range(D)]
A=s.Matrix([[2*a[-1],a[-2]-a[0],a[-4]-a[1]],[a[-2]-a[0],2*a[-3],a[-5]-a[2]],[a[-4]-a[1],a[-5]-a[2],2*a[-6]]])
B=s.Matrix([[2*a[-1],a[-2]-a[0],a[-3]-a[1]],[a[-2]-a[0],2*a[-4],a[-5]-a[2]],[a[-3]-a[1],a[-5]-a[2],2*a[-6]]])
coeff={}
for entry in j['terms']:
 c=s.Rational(entry['coefficient']);assert c>0
 name=entry['name']
 if name.startswith('gprod'):
  inds=ast.literal_eval(name[5:]);m=tuple(inds.count(i) for i in range(D));coeff[m]=coeff.get(m,0)+c;continue
 M={'A':A,'B':B}[name[0]];tail=name[1:]
 if tail=='det':expr=M.det()
 elif (m:=re.fullmatch(r'minor(\d)(\d)\*g(\d+)',tail)):
  u,v,k=map(int,m.groups());expr=(M[u,u]*M[v,v]-M[u,v]**2)*g[k-1]
 else:
  m=re.fullmatch(r'quad(\([^)]*\))\*g(\d+)g(\d+)',tail);assert m,name
  v=s.Matrix(ast.literal_eval(m[1]));u,w=int(m[2])-1,int(m[3])-1;expr=(v.T*M*v)[0]*g[u]*g[w]
 for m,x in s.Poly(s.expand(expr),g).terms():coeff[m]=coeff.get(m,0)+c*x
T=sum(a);Q=(D+8)*T*T-(D+2)**2*sum(x*x for x in a) if D<=24 else 9*T*T-8*D*sum(x*x for x in a)
expected=dict(s.Poly(s.expand(Q*T),g).terms())
assert {m:c for m,c in coeff.items() if c}==expected
print('PASS independent SymPy checker D=',D,'terms=',len(j['terms']),flush=True)
