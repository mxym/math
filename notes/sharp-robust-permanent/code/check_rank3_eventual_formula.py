#!/usr/bin/env python3
# Standalone exact symbolic verifier of four rational optimality branches for S_n on 3-subsets.
# Reconstructs all primal weights and orbital dual coefficients from 5x5 rational
# moment equations, and verifies strict positivity by integer polynomial Taylor
# coefficients in q=m-M. No numerical LP, heuristics, or floating point.
import json
from pathlib import Path
import sys
import sympy as s
m=s.symbols("m", integer=True, positive=True)

def F(n,x,y,z):
    N=n*(n-1)*(n-2)/6
    M1=(n-2)*(2*n+(n-3)*x)/2
    M2=(n-2)*x*(x-1)/2+(x+1)*(n-x)+(n-4)*y
    M3=x*(x-1)*(x-2)/6+x*y+z
    return [s.expand(N-M1+M2-M3),
            s.expand(M1-2*M2+3*M3),
            s.expand(M2-3*M3),
            s.expand(M3)]

def supports(r):
    n=4*m+r
    K=[3*m-2,3*m-1,3*m-1,3*m][r]
    pair_cycles=[2*m,2*m-1,2*m+1,2*m][r]
    triple_cycles=[0,1,0,1][r]
    E_x=[m-3,m-2,m-2,m-2][r]
    E_z=[m+1,m+1,m,m][r]
    return n,[(n,0,0),(K,0,0),(0,pair_cycles,triple_cycles)],[(n-2,1,0),(E_x,0,E_z)]

def solve(r):
    n,P,Q=supports(r)
    allT=P+Q
    A=s.Matrix([[1,1,1,0,0],[0,0,0,1,1]]+
      [[F(n,*a)[j]*(1 if i<3 else -1) for i,a in enumerate(allT)] for j in range(3)])
    assert A.det()!=0
    w=[s.factor(v) for v in (A.inv()*s.Matrix([1,1,0,0,0]))]
    B=s.Matrix([F(n,*a)[:3]+([1,0] if i<3 else [0,1]) for i,a in enumerate(allT)])
    assert B.det()!=0
    d=[s.factor(v) for v in (B.inv()*s.Matrix([1,0,0,0,0]))]
    return n,P,Q,w,d

import sympy as s
x,y,z,t,q=s.symbols('x y z t q')
def polytest(expr,M,tag):
 e=s.cancel(expr)
 num,den=s.fraction(e)
 ne=s.Poly(s.expand(num.subs(m,q+M)),q)
 de=s.Poly(s.expand(den.subs(m,q+M)),q)
 if de.eval(0)<0: ne=-ne;de=-de
 ok=all(c>=0 for c in ne.all_coeffs()) and all(c>=0 for c in de.all_coeffs()) and de.eval(0)>0
 return ok, [s.factor(e),list(reversed(ne.all_coeffs()))]

def main():
 certificate={'scope':'Four exact rational branches for k=3; positivity of all reduced integer-polynomial expressions after q=m-M shift','sympy_version':s.__version__,'residues':[]}
 for r in range(4):
  n,P,Q,w,d=solve(r)
  assert len(set(P+Q))==5
  for typ in P+Q:
   residual=s.factor(n-typ[0]-2*typ[1]-3*typ[2])
   # Short-cycle type is admissible if residual is zero or at least four,
   # as can be checked by its affine expression on m>=M.
   assert residual==0 or residual.subs(m,12)>=4 and s.diff(residual,m)>=0
  raw=s.cancel(-sum(d[i]*F(n,x,y,z)[i] for i in range(3)))
  N,D=s.fraction(raw)
  if D.subs(m,12)<0:N=-N;D=-D
  assert not (D.free_symbols-{m})
  L=s.cancel(D*d[4])
  assert s.simplify(N.subs({x:n,y:0,z:0}))==0
  E=Q[1][0]; K=P[1][0]; T=n-2
  startUpper={0:2*m-4,1:2*m-3,2:2*m-3,3:2*m-2}[r]
  startLower={0:2*m-3,1:2*m-3,2:2*m-2,3:2*m-2}[r]
  BY=s.diff(N,y); BZ=s.diff(N,z); BL=BY-s.Rational(2,3)*BZ
  checks={}
  candidate_types=P+Q
  primal_mat=s.Matrix([[1,1,1,0,0],[0,0,0,1,1]]+
    [[F(n,*c)[j]*(1 if i<3 else -1) for i,c in enumerate(candidate_types)] for j in range(3)])
  dual_mat=s.Matrix([F(n,*c)[:3]+([1,0] if i<3 else [0,1]) for i,c in enumerate(candidate_types)])
  assert s.simplify(primal_mat.det()+dual_mat.det())==0
  checks['primal matrix nonzero negative determinant']=-primal_mat.det()
  checks['dual matrix nonzero positive determinant']=dual_mat.det()
  checks['positive D']=D
  checks['z decreasing']=-BZ
  assert not (BZ.free_symbols - {m})
  checks['both y slopes decreasing']=-s.diff(BY,x)
  checks['upper y positive']=BY.subs(x,startUpper)
  checks['upper y negative']=-BY.subs(x,startUpper+1)
  checks['lower y positive']=3*BL.subs(x,startLower)
  checks['lower y negative']=-3*BL.subs(x,startLower+1)
  # Upper small x: 1-h(x,(n-x)/2,0), quadratic / x after subtracting U(0)
  Uup=s.cancel(D-N.subs({y:(n-x)/2,z:0}))
  U0=s.factor(Uup.subs(x,0))
  Uq=s.factor((Uup-U0)/x)
  assert s.Poly(Uq,x).degree()==2
  Aup,Bup,Cup=s.Poly(s.expand(Uq),x).all_coeffs()
  checks['upper early A positive']=Aup
  checks['upper early derivative nonpos']=-s.diff(Uq,x).subs(x,startUpper)
  checks['upper early Q+U0 positive']=Uq.subs(x,startUpper)+U0
  if r%2:
   checks['upper odd continuous x0 is below upper']=-U0
   checks['upper odd x0 feasible bound']=D-N.subs({x:0,y:(n-5)/2,z:0})
   assert s.simplify(N.subs({x:0,y:(n-3)/2,z:1})-D)==0
  else:
   assert s.simplify(U0)==0
  # upper large x
  Ulo=s.cancel((D-N.subs({y:0,z:0})).subs(x,K+t)/t)
  assert s.Poly(Ulo,t).degree()==2
  Au,Bu,Cu=s.Poly(s.expand(Ulo),t).all_coeffs()
  left=(startUpper+1)-K
  checks.update({
   'upper late A':Au,'upper late B':Bu,'upper late Q(1) positive':Ulo.subs(t,1),
   'upper late Q(-1) negative':-Ulo.subs(t,-1),
   'upper late Q(left) negative':-Ulo.subs(t,left)
  })
  # lower small x at z relaxed max
  Lle=s.cancel((N.subs({y:0,z:(n-x)/3})-L).subs(x,E+t))
  qpoly=s.Poly(s.expand(Lle),t)
  assert qpoly.degree()==3
  A3,B2,C1,Z0=qpoly.all_coeffs()
  # expect -A*t^3+B*t^2-C*t+Z0.
  if r in (0,1):
   assert s.simplify(Z0)==0
  else:
   checks['lower early exceptional constant negative']=-Z0
  checks.update({
   'lower early -A':-A3, 'lower early B':B2,
   'lower early C sign': (C1 if r==1 else -C1),'lower early L(-1)':Lle.subs(t,-1)
  })
  qsmall=-(-A3)*t*t+B2*t+C1
  # same A3*t*t+B2*t+C1 = lower cubic except constant
  assert s.simplify(Lle - (Z0+t*qsmall))==0
  Tmax=startLower-E
  checks['lower early D0+2Q(2)']=Z0+2*qsmall.subs(t,2)
  checks['lower early D0+2Q(Tmax)']=Z0+2*qsmall.subs(t,Tmax)
  # exceptions t=0,1. For fixed x=E+t and y=0, minimal leftover is
  # 0 if divisible3, otherwise 4/5; the max possible z yields it.
  for tt in [0,1]:
   xx=E+tt
   rem=s.simplify(n-xx)
   # sympy integer m, residues fixed because n-E constant modulo3
   rr=int(rem.subs(m,12))%3
   rmin={0:0,1:4,2:5}[rr]
   assert (rem-rmin).subs(m,12)>=0
   checks[f'lower exceptional t{tt} y>=1']=3*(Lle.subs(t,tt)+BL.subs(x,xx))
   checks[f'lower exceptional t{tt} y=0']=3*Lle.subs(t,tt)-rmin*BZ
  # lower large x at y relaxed maximum
  Lhi=s.cancel((N.subs({y:(n-x)/2,z:0})-L).subs(x,T-t)/t)
  assert s.Poly(Lhi,t).degree()==2
  Al,Bl,Cl=s.Poly(s.expand(Lhi),t).all_coeffs()
  Tmax=T-(startLower+1)
  checks['lower late A positive']=Al
  checks['lower late derivative nonpos']=-s.diff(Lhi,t).subs(t,Tmax)
  checks['lower late Q(Tmax) positive']=Lhi.subs(t,Tmax)

  for j in range(5):
   checks[f'dual component{j} defined denominator']=s.denom(s.factor(d[j]))
  # primal is defined by exact 5x5 matching matrix -- check positivity
  for i,wi in enumerate(w): checks[f'primal weight{i} positive']=wi
  assert s.simplify(sum(w[:3])-1)==0
  assert s.simplify(sum(w[3:])-1)==0
  for j in range(3):
   lhs=sum(w[i]*F(n,*P[i])[j] for i in range(3))
   rhs=sum(w[3+i]*F(n,*Q[i])[j] for i in range(2))
   assert s.simplify(lhs-rhs)==0
  assert s.simplify(w[0]-(1-d[4]))==0
  for i,profile in enumerate(P+Q):
   val=int(i==0)-sum(d[j]*F(n,*profile)[j] for j in range(3))
   assert s.simplify(val-(d[3] if i<3 else d[4]))==0,(r,i)
  M=12 if r in (1,3) else 6
  assert s.simplify(sum(w[:3])-1)==0
  assert s.simplify(sum(w[3:])-1)==0
  bad=[]
  sign_records=[]
  for tag,expr in checks.items():
   ok,info=polytest(expr,M,tag)
   reduced=s.cancel(expr)
   numerator,denominator=s.fraction(reduced)
   NP=s.Poly(s.expand(numerator.subs(m,q+M)),q)
   DP=s.Poly(s.expand(denominator.subs(m,q+M)),q)
   if DP.eval(0)<0: NP=-NP;DP=-DP
   sign_records.append({'name':tag,
       'numerator_q_coefficients':[str(c) for c in reversed(NP.all_coeffs())],
       'denominator_q_coefficients':[str(c) for c in reversed(DP.all_coeffs())]})
   if not ok:bad.append((tag,info[0],info[1]))
  certificate['residues'].append({'r':r,'threshold_m':M,
   'class_profiles':{'P':[[str(u) for u in cls] for cls in P],
                     'Q':[[str(u) for u in cls] for cls in Q]},
   'optimal_value':str(s.factor(w[0])),
   'positive_primal_weights':[str(s.factor(v)) for v in w],
   'dual_parameters':[str(s.factor(v)) for v in d],
   'sign_conditions':sign_records})
  print('RESIDUE',r,'THRESHOLD',M,'nchecks',len(checks),'FAILED',len(bad),flush=True)
  print(' EXPLICIT OPTIMUM',s.factor(w[0]),flush=True)
  for name,formula,coef in bad[:30]:print(' FAILURE',name,'expr=',formula,'Taylor=',coef,flush=True)
  if bad:
   for alt in (10,12,20,30,40,60,100):
    fails=[tag for tag,expr in checks.items() if not polytest(expr,alt,tag)[0]]
    print(' alternative threshold',alt,'failures',len(fails),fails[:6],flush=True)
 expected_path=Path(__file__).resolve().parents[1]/'certificates'/'three_subset_eventual_4branch_signs.json'
 if '--emit' in sys.argv:
  expected_path.parent.mkdir(parents=True,exist_ok=True)
  expected_path.write_text(json.dumps(certificate,indent=2,sort_keys=True)+'\n',encoding='utf-8')
  print('CERTIFICATE WRITTEN',expected_path)
 else:
  assert expected_path.is_file(),f'Missing frozen certificate: {expected_path}'
  pinned=json.loads(expected_path.read_text(encoding='utf-8'))
  assert pinned==certificate,'Symbolic proof does not match frozen rational sign certificates'
  print('ALL FOUR EVENTUAL BRANCHES EXACTLY REPLAYED FROM FROZEN SIGN CERTIFICATE')

if __name__=='__main__':main()
