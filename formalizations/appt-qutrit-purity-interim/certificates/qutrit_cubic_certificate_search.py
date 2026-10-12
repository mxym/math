"""Search for a verifiable nonnegative-polynomial certificate, not a proof itself.
Target (17 (sum lambda)^2 -121 sum lambda^2)*sum lambda >=0.
Necessary APPT matrices are Eq7/9 of arXiv:2603.20717v1.
A floating LP result is never accepted without exact rational reconstruction.
"""
import sympy as s, numpy as np, itertools, json
from scipy.optimize import linprog
from pathlib import Path
g=s.symbols('g1:10'); lam=[sum(g[i:]) for i in range(9)]
a=lam
A=s.Matrix([[2*a[8],a[7]-a[0],a[5]-a[1]],[a[7]-a[0],2*a[6],a[4]-a[2]],[a[5]-a[1],a[4]-a[2],2*a[3]]])
B=s.Matrix([[2*a[8],a[7]-a[0],a[6]-a[1]],[a[7]-a[0],2*a[5],a[4]-a[2]],[a[6]-a[1],a[4]-a[2],2*a[3]]])
T=sum(lam); target=s.Poly(s.expand((17*T*T-121*sum(x*x for x in lam))*T),g)
mons=[tuple(sum(1 for z in inds if z==i) for i in range(9)) for inds in itertools.combinations_with_replacement(range(9),3)]
idx={m:i for i,m in enumerate(mons)}
cols=[]; names=[]; polys=[]
def add(p,name):
 p=s.Poly(s.expand(p),g); v=np.zeros(len(mons))
 for m,c in p.terms():v[idx[m]]=float(c)
 if np.linalg.norm(v)==0:return
 cols.append(v);names.append(name);polys.append(p)
for inds in itertools.combinations_with_replacement(range(9),3):add(s.prod(g[i] for i in inds),f'gprod{inds}')
for label,M in [('A',A),('B',B)]:
 add(M.det(),label+'det')
 for i,j in itertools.combinations(range(3),2):
  minor=M[i,i]*M[j,j]-M[i,j]**2
  for k in range(9):add(minor*g[k],f'{label}minor{i}{j}*g{k+1}')
 for v in itertools.product(range(3),repeat=3):
  if not any(v):continue
  # nonnegative eigenvectors suffice because all offdiagonal M entries <=0
  if s.igcd(*v)!=1:continue
  x=s.Matrix(v); l=(x.T*M*x)[0]
  for i,j in itertools.combinations_with_replacement(range(9),2):add(l*g[i]*g[j],f'{label}quad{v}*g{i+1}g{j+1}')
y=np.array([float(target.coeff_monomial(m)) for m in mons]); mat=np.array(cols).T
print('shape',mat.shape,flush=True)
cost=np.array([0.0001 if name.startswith("gprod") else 1.0 for name in names])
r=linprog(cost,A_eq=mat,b_eq=y,bounds=[(1 if name in {f"gprod({i}, {i}, {i})" for i in range(1,8)} else 0,None) for name in names],method='highs',options={'time_limit':90})
print('status',r.status,r.message,flush=True)
out={'status':int(r.status),'message':r.message,'is_proof':False}
if r.success:
 lower=np.array([1 if name in {f"gprod({i}, {i}, {i})" for i in range(1,8)} else 0 for name in names],dtype=int)
 free=np.flatnonzero(r.x-lower>1e-7)
 active=np.flatnonzero(r.x>1e-7)
 try:
  sol, params=s.Matrix(mat[:,free].astype(int)).gauss_jordan_solve(s.Matrix((y-mat@lower).astype(int)))
  sol=sol.subs({p:0 for p in params})
  values={i:s.Rational(int(lower[i])) for i in active}
  for i,v in zip(free,sol):values[i]=values.get(i,s.Integer(0))+v
  active=np.array(sorted(values));coeff=[values[i] for i in active]
 except ValueError:
  coeff=[s.Rational(float(r.x[i])).limit_denominator(10**8) for i in active]
 residual=target-sum((c*polys[i] for i,c in zip(active,coeff)),s.Poly(0,g))
 exact=residual.is_zero and all(c>=0 for c in coeff)
 out.update(exact_certificate=bool(exact),terms=[{'name':names[i],'coefficient':str(c)}for i,c in zip(active,coeff)],max_residual=float(np.max(np.abs(mat@r.x-y))))
 print('active',len(active),'exact',exact,flush=True)
 if exact:
  out['is_proof']=True
  out['identity']=str(sum((c*polys[i].as_expr() for i,c in zip(active,coeff)),s.Integer(0)))
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
