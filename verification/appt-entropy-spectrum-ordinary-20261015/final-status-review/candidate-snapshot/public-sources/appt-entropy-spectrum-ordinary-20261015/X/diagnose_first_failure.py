"""Diagnose the retained first reviewer control FAIL without changing that run."""
from pathlib import Path
import hashlib
import json
import runpy
import traceback

here = Path(__file__).resolve().parent
old = here/'runs/20261015T135229.946566Z/independent_checks.py'
namespace = runpy.run_path(str(old), run_name='reviewer_diagnosis_only')
record = {'first_script_sha256': hashlib.sha256(old.read_bytes()).hexdigest(),
          'source': str(old), 'author_code_executed': False}
try:
    namespace['scalars']()
except AssertionError as exc:
    tb = exc.__traceback__
    while tb.tb_next:
        tb = tb.tb_next
    local = tb.tb_frame.f_locals
    mp = local['mp']
    record.update({'reproduced_AssertionError': True, 'failing_line': tb.tb_lineno,
                   'm': local['m'], 'D': local['D'], 'alpha': str(local['a']),
                   'pole_times_D_over_alpha': mp.nstr(local['pb']*local['D'], 90),
                   'unsupported_reviewer_threshold': 10,
                   'derived_bound_for_alpha_up_to_7': mp.nstr(mp.mpf(3)**7*mp.log(3)**2, 90),
                   'derivation': 'J_D(0)=J_D(1)=0; interpolation remainder |J_D/[a(a-1)]|<=sup|J_D_second|/2. J_D_second=(log3)^2(D-1)3^a/(D-1+3^a)^2 <= (log3)^2 3^7/(D-1). For D>=2, (D/(2(D-1)))<=1, so p_D D/a<=3^7(log3)^2. The source only claims an unspecified compact-order C_A, not 10.',
                   'scope': 'Reviewer finite-control constant correction; no manuscript or author-source change.'})
else:
    raise RuntimeError('Original failure did not reproduce.')
dest = here/'FIRST_REVIEWER_CONTROL_FAILURE.json'
assert not dest.exists()
dest.write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record, indent=2))
