"""Preserve a source-bound complete author packet, without publication or review promotion."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, zipfile

base = Path(__file__).resolve().parent
target = base / 'AUTHOR_V1_MANIFEST.json'
if target.exists():
    raise RuntimeError('Do not overwrite a frozen author packet')
run = base / 'control-runs/20261015T132659.576684Z/RESULT.json'
result = json.loads(run.read_text())
assert result['status'] == 'PASS'
paper = base / 'PAPER.md'
paper_sha = hashlib.sha256(paper.read_bytes()).hexdigest()
assert paper_sha == result['source_hashes']['PAPER.md']
files = {str(p.relative_to(base)): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in base.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix != '.pyc'}
now = datetime.now(timezone.utc)
manifest = {'utc': now.isoformat(), 'kind': 'complete author proof and finite author controls, independent review pending',
            'source_commit_of_credited_inputs': '1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f',
            'paper_sha256': paper_sha, 'paper_bytes': paper.stat().st_size,
            'files': files, 'first_control_run_status': 'PASS', 'unexpected_control_failures': 0,
            'new_Lean_executions': 0, 'new_major_result_count': 0, 'published': False}
target.write_text(json.dumps(manifest, indent=2) + '\n')
archive = base.parent / ('all-dimension-positive-entropy-owner-v1-' + now.strftime('%Y%m%dT%H%M%SZ') + '.zip')
with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED) as z:
    for rel in files:
        z.write(base / rel, 'all-dimension-positive-entropy-20261015/' + rel)
    z.write(target, 'all-dimension-positive-entropy-20261015/' + target.name)
receipt = {'utc': now.isoformat(), 'owner_archive': str(archive),
           'owner_archive_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
           'manifest_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
           'paper_sha256': paper_sha, 'files': len(files), 'status': 'FROZEN_AUTHOR_ONLY'}
(base / 'OWNER_V1_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
