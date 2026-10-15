"""Standalone exact control for the independently found theta=0 wording defect."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil
import sympy as s

base = Path(__file__).resolve().parent
run = base / 'endpoint-control-runs' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True)
for name in ('PAPER.md', 'endpoint_derivative_control.py', 'V2_REVIEW_FINDING.json'):
    shutil.copyfile(base/name, run/name)
alpha, theta, k, z = s.symbols('alpha theta k z', real=True)
# z=(1+k)^(alpha-1); differentiation has used d(1+k)^alpha/dk=alpha*z.
num = 1+theta*((1+k)*z-1)
den = 1+k*theta
actual = alpha*theta*z/num-alpha*theta/den
claimed = alpha*theta*(1-theta)*(z-1)/(num*den)
assert s.factor(actual-claimed) == 0
assert s.simplify(actual.subs(theta,0)) == 0
assert s.simplify(actual.subs(theta,1)) == 0
assert s.simplify(actual.subs(z,1)) == 0
# The old claimed sign proxy can be strictly positive while the derivative is zero.
assert ((1-theta)*(z-1)).subs({theta:0,z:2}) == 1
assert claimed.subs({alpha:2,theta:0,k:1,z:2}) == 0
result = {'utc': datetime.now(timezone.utc).isoformat(), 'status': 'PASS',
          'exact_symbolic_and_endpoint_assertions': 6,
          'purpose': 'Control for the v1 endpoint wording correction, not an independent theorem review',
          'source_hashes': {n:hashlib.sha256((base/n).read_bytes()).hexdigest()
                            for n in ('PAPER.md','endpoint_derivative_control.py','V2_REVIEW_FINDING.json')}}
(run/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'run':str(run),**result}))
