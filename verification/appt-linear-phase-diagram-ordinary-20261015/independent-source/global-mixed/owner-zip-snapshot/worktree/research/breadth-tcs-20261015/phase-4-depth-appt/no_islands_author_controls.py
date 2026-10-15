from pathlib import Path
import datetime as dt
import hashlib
import json
import sympy as sp
import mpmath as mp

t,E,z=sp.symbols('t E z',positive=True)
q=t/(E-1)
d=1-q
s=1-d/t
gp=s*d
def D(expr):return sp.diff(expr,t)+E*sp.diff(expr,E)
gpp=D(gp)
elastic=t*D(d)/d
ode_rhs=-elastic+q*(elastic+q)*(1-elastic)/((1-q)*elastic)
identities={
 'curvature_qz_identity':sp.factor(t*gpp/gp-(q*(t-d)/d-q+d/(t-d)))==0,
 'elasticity_w_ode':sp.factor(D(elastic)/s-ode_rhs)==0,
 'q_second_derivative':sp.factor(D(D(q))-E*((t-2)*E+t+2)/(E-1)**3)==0,
}
R=32*z**4-96*z**3+86*z**2-20*z-1
Rraw=4*(5-4*z)*(3-2*z)*z*(z-sp.Rational(1,4))-z*(5-4*z)-1
identities['barrier_polynomial']=sp.expand(R-Rraw)==0
identities['barrier_second_derivative']=sp.expand(sp.diff(R,z,2)+20-384*(z-sp.Rational(1,2))*(z-1))==0
identities['barrier_endpoints']=(R.subs(z,sp.Rational(1,2))==sp.Rational(1,2) and R.subs(z,1)==1)
assert all(identities.values()),identities

mp.mp.dps=95
def data(a):
    Q=a/mp.expm1(a)
    DD=1-Q
    S=1-DD/a
    W=-mp.log(Q)
    G=W-DD
    return Q,DD,S,W,G,S*DD
checks=[]
for xstr in ['0.0001','0.001','0.01','0.05','0.1','0.25','0.5','0.75','0.9','0.99','0.9999']:
    x=mp.mpf(xstr)
    for Kstr in ['0.0001','0.001','0.01','0.05','0.1','0.2','0.4','0.52','0.8','1','2','5','10','20']:
        K=mp.mpf(Kstr); k=x*K
        Q,DD,S,W,G,GP=data(k)
        QK,DK,SK,WK,GK,GPK=data(K)
        v=W-GK
        if v<=0:continue
        delta=GK-G
        delta_prime=GPK-x*GP
        norm_log_derivative=delta_prime/delta-2*x*S*Q/DD
        h_log_derivative=delta_prime/delta+x*S-GPK/(-mp.expm1(-GK))
        assert norm_log_derivative>0 and h_log_derivative>0
        h=delta/(Q*mp.expm1(GK))
        h_represented=delta/(delta+mp.expm1(-v)+v)
        assert abs(h-h_represented)<mp.mpf('1e-75')
        checks.append({'x':xstr,'K':Kstr,
                      'admissible_v':mp.nstr(v,40),
                      'normalized_delta_log_derivative':mp.nstr(norm_log_derivative,40),
                      'H_log_derivative':mp.nstr(h_log_derivative,40)})
paper=Path(__file__).with_name('NO_ISLANDS.md')
out={'utc':dt.datetime.now(dt.timezone.utc).isoformat(),
     'scope':'Author control only, not independent review, interval certification or Lean',
     'paper_sha256':hashlib.sha256(paper.read_bytes()).hexdigest(),
     'exact_rational_algebra_identities':identities,
     'finite_floating_checks':checks,
     'finite_checks_do_not_prove_global_claim':True,
     'proof_global_inequalities':'Human-readable analytic argument in exact bound paper bytes',
     'result':'All requested symbolic identities and selected finite falsification controls passed'}
dest=Path(__file__).with_name('NO_ISLANDS_AUTHOR_CONTROL.json')
dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':out['paper_sha256'],'exact_identities':identities,
                  'finite_admissible_points':len(checks),'result':out['result']},indent=2))
