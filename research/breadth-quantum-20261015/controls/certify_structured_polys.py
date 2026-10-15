"""Exact Bernstein sign certificates on the full gray parameter interval."""
from pathlib import Path
import json,argparse,datetime
import sympy as sp
ap=argparse.ArgumentParser();ap.add_argument('--input',required=True);ap.add_argument('--output',required=True);args=ap.parse_args()
assert Path(args.output).is_absolute(),'use an absolute output path'
P=Path(args.output).resolve();assert not P.exists(),'choose a new evidence output'
source=json.loads(Path(args.input).read_text());lam,t=sp.symbols('lam t',real=True);rows=[]
for rec in source['records']:
    pol=sp.sympify(rec['unnormalized_four_input_copy_witness_polynomial'].replace('lambda','lam'),locals={'lam':lam});new=sp.Poly(sp.expand(pol.subs(lam,(2+t)/6)),t);n=new.degree()
    bern=[sp.simplify(sum(new.nth(j)*sp.binomial(i,j)/sp.binomial(n,j) for j in range(i+1))) for i in range(n+1)]
    assert all(x>0 for x in bern),(rec,bern)
    identity=sp.expand(sum(bern[i]*sp.binomial(n,i)*t**i*(1-t)**(n-i) for i in range(n+1))-new.as_expr());assert identity==0
    rows.append({'A_code':rec['A_code'],'B_code':rec['B_code'],'degree':n,'bernstein_coefficients':[str(x) for x in bern],'strict_lower_bound_on_gray_interval':str(min(bern))})
out={'schema':'exact-restricted-protocol-interval-sign-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lambda_interval':['1/3','1/2'],'parameter_change':'lambda=(2+t)/6, 0<=t<=1','scope':'Only the16 stated two-copy-to-qutrit filters followed by the attributed fixed canonical witness on two independent outputs. These cannot give a negative four-input-copy expectation anywhere in the entire gray interval. No all-filter or all-copy inference.','rows':rows,'complete_target_solved':False}
P.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'families_certified':len(rows),'minimum_bound':str(min(sp.Rational(r['strict_lower_bound_on_gray_interval']) for r in rows)),'output':str(P)}))
