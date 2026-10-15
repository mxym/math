"""Run new reviewer controls, preserving every real return code/output/script byte."""
from pathlib import Path
import datetime as dt
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run = HERE / 'runs' / stamp
run.mkdir(parents=True)
source = HERE / 'independent_checks.py'
(run / source.name).write_bytes(source.read_bytes())
(run / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
jobs = [('symbolic_exact', ['exact'], 0), ('noninteger_and_log', ['real'], 0)]
jobs += [(x, ['variant', '--name', x], 1) for x in
         ('branch_minimum', 'omit_J', 'omit_mean_square', 'unweighted_W2', 'entropy_requires_moment', 'log_coarse_error')]
rows = []
for name, args, expected in jobs:
    proc = subprocess.run([sys.executable, str(run/source.name)] + args, capture_output=True, text=True)
    (run/(name+'.stdout')).write_text(proc.stdout)
    (run/(name+'.stderr')).write_text(proc.stderr)
    okay = proc.returncode == expected and (expected == 0 or 'AssertionError:' in proc.stderr)
    row = {'name': name, 'command_argv': [sys.executable, 'independent_checks.py']+args,
           'returncode': proc.returncode, 'expected_returncode': expected, 'checked': okay,
           'negative_control': expected != 0}
    rows.append(row)
    print(json.dumps(row), flush=True)
result = {'status': 'PASS' if all(x['checked'] for x in rows) else 'FAIL',
          'utc': dt.datetime.now(dt.timezone.utc).isoformat(),
          'script_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'paper_sha256': 'da596b457eb4d2b82a1d231de065d07197def79414be0aaa1c1f069505e8e74b',
          'authorship': 'Reviewer-authored helper and harness; no imports or execution of author code.',
          'author_controls_rerun': False, 'all_jobs': rows,
          'mathematical_scope': 'Supporting finite checks, not a substitute for full analytic review or a quantified certificate.'}
(run/'RESULT.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'run': str(run), 'status': result['status']}, indent=2))
sys.exit(0 if result['status'] == 'PASS' else 1)
