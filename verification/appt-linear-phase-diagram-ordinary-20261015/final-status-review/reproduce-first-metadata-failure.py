"""Reproduce and retain the actual first stdin checker condition; no math replay."""
from pathlib import Path
import datetime as dt
import hashlib
import json
import subprocess
import sys

here = Path(__file__).resolve().parent
run = here/'metadata-runs'/dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True)
source = here/'first-source-comparison.py'
(run/source.name).write_bytes(source.read_bytes())
proc = subprocess.run([sys.executable, str(source)], capture_output=True, text=True)
(run/'stdout').write_text(proc.stdout)
(run/'stderr').write_text(proc.stderr)
assert proc.returncode == 1 and 'AssertionError' in proc.stderr
record = {'utc': dt.datetime.now(dt.timezone.utc).isoformat(), 'initial_execution': 'Earlier actual terminal stdin execution, saved here verbatim as first-source-comparison.py; this is a preserved same-source reproduction.',
          'actual_original_tool_chunk': None, 'original_tool_chunk_note': 'Not captured: original exec wrapper forwarded output text only.', 'initial_exit_code': 1,
          'reproduction_returncode': proc.returncode,
          'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'finding': 'Unfiltered reviewer file-set equality included15 generated __pycache__/*.pyc files absent from the public source evidence. All186 durable files match exactly; no durable source/report/result is missing.',
          'resolution': 'Only explicit interpreter bytecode caches may be excluded from the durable-source comparison; retain all raw original files privately. No certificate or mathematics rerun.',
          'source_or_candidate_modified': False}
(run/'RESULT.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({'run': str(run), **record}, indent=2))
