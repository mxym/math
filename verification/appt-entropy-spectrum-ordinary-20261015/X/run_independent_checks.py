"""Reviewer harness retaining real successes/failures and literal executed source."""
from pathlib import Path
import datetime as dt
import hashlib
import json
import subprocess
import sys

here = Path(__file__).resolve().parent
stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run = here/'runs'/stamp
run.mkdir(parents=True)
for name in ('independent_checks.py', Path(__file__).name):
    (run/name).write_bytes((here/name).read_bytes())
jobs = [('symbolic_and_qubit', ['exact'], 0), ('uniform_scalars', ['scalars'], 0)]
names = ['v1_derivative_sign_at_theta_zero', 'omit_hole_floor', 'replace_finite_m_bulk',
         'replace_sum_by_max', 'omit_surplus', 'continuous_rank_is_exact',
         'operator_convexity_substitute', 'extend_C_outside_domain']
jobs += [(n, ['wrong', '--name', n], 1) for n in names]
rows = []
for name, args, expected in jobs:
    proc = subprocess.run([sys.executable, str(run/'independent_checks.py')]+args, capture_output=True, text=True)
    (run/(name+'.stdout')).write_text(proc.stdout)
    (run/(name+'.stderr')).write_text(proc.stderr)
    okay = proc.returncode == expected and (expected == 0 or 'AssertionError: False:' in proc.stderr)
    row = {'name': name, 'returncode': proc.returncode, 'expected_returncode': expected,
           'checked': okay, 'negative_control': expected != 0}
    rows.append(row)
    print(json.dumps(row), flush=True)
result = {'status': 'PASS' if all(x['checked'] for x in rows) else 'FAIL',
          'utc': dt.datetime.now(dt.timezone.utc).isoformat(),
          'reviewer_script_sha256': hashlib.sha256((run/'independent_checks.py').read_bytes()).hexdigest(),
          'reviewed_current_paper_sha256': 'b7d51f6b49ab2fb35245883f18f81d5bee478c4fcb707681437ffd7ebc1ddec2',
          'authorship': 'Reviewer-written helper and harness, no author imports/AST/execution.',
          'jobs': rows, 'not_an_infinite_proof_or_global_optimizer_certificate': True}
(run/'RESULT.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'run': str(run), 'status': result['status']}))
sys.exit(0 if result['status'] == 'PASS' else 1)
