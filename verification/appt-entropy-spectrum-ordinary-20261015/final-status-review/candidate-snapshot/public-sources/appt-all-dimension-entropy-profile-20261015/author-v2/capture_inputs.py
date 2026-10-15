"""Freeze exact credited local sources for Theorem X; no mathematical or Lean execution."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess

out = Path(__file__).resolve().parent
root = Path('/home/mxym/math-appt-multiscale-20261013')
head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD']).decode().strip()
expected = '1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
if head != expected:
    raise RuntimeError('Source base changed; explicitly reconcile it before capture')
dest = out / 'credited-inputs'
if dest.exists():
    raise RuntimeError('Do not overwrite credited inputs')
rels = [
    'research/appt-growing-renyi/ALL_ORDER_VARIATIONAL.md',
    'research/appt-growing-renyi/ALL_ORDER_REVIEW.json',
    'research/appt-growing-renyi/UNIFORM_PROFILE.md',
    'research/appt-growing-renyi/PAPER.md',
    'research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md',
    'research/appt-growing-renyi/LINEAR_ORDER_REVIEW.json',
    'research/appt-all-order-exact-20261014/PAPER.md',
    'research/appt-all-order-exact-20261014/REVIEW.md',
    'research/appt-all-order-exact-20261014/REVIEW.json',
    'research/appt-sharp-log-cutoff-20261014/PAPER.md',
    'research/appt-sharp-log-cutoff-20261014/MANUSCRIPT_REVIEW.json',
    'research/appt-zero-order-transition-20261014/PAPER.md',
    'research/appt-zero-order-transition-20261014/REVIEW.json',
    'research/appt-all-positive-axis-20261014/PAPER.md',
    'research/appt-finite-entropy-bounds-20261015/PAPER.md',
    'research/appt-finite-entropy-bounds-20261015/REVIEW.json',
    'research/appt-cutoff-root-tracking-20261014/PAPER.md',
    'research/appt-critical-window-20261014/PAPER.md',
    'research/appt-multilevel-counterexample/SUBUNIT_ALL_DIMENSIONS.md',
    'research/appt-log-order-phase-20261014/LOG_POWER_ENVELOPE.md',
]
records = {}
for rel in rels:
    data = subprocess.check_output(['git', '-C', str(root), 'show', head + ':' + rel])
    if (root / rel).read_bytes() != data:
        raise RuntimeError('Live source differs from immutable source ' + rel)
    target = dest / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    records[rel] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data),
                    'git_blob': subprocess.check_output(['git', '-C', str(root), 'rev-parse', head + ':' + rel]).decode().strip()}
record = {'utc': datetime.now(timezone.utc).isoformat(), 'source_commit': head,
          'kind': 'frozen ordinary theorem inputs and exact earlier review scopes; not a new audit of them',
          'files': records, 'new_Lean_executions': 0, 'independent_review_of_X_pending': True}
(out / 'CREDITED_INPUTS.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'source_commit': head, 'frozen_input_files': len(records), 'new_Lean_executions': 0}))
