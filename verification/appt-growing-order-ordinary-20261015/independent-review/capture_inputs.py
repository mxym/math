"""Freeze P sources and exact finite graph proof inputs; run no controls."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess

HERE = Path(__file__).resolve().parent
STAGE = HERE.parent
AUTHOR = STAGE / 'growing-renyi-order'
REPO = Path('/home/mxym/math-appt-multiscale-20261013')
manifest = {'captured_utc': datetime.now(timezone.utc).isoformat(), 'files': {}}

def copy(source, destination):
    data = source.read_bytes(); target = HERE / destination
    if target.exists():
        assert target.read_bytes() == data, str(target)
    else:
        target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
    manifest['files'][destination] = {'source': str(source),
        'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data),
        'lines': len(data.splitlines())}

for name in ['PAPER.md', 'THEOREM_MAP.md']:
    copy(AUTHOR / name, 'snapshot/P/' + name)
old_C = STAGE / 'independent-entropy-review-resume' / 'snapshot' / 'dependencies' / 'appt-cubic-entropy-20261014.md'
copy(old_C, 'snapshot/dependencies/C-PAPER.md')
tracked = subprocess.run(['git', '-C', str(REPO), 'ls-files', '-z'],
                          check=True, stdout=subprocess.PIPE).stdout.split(b'\0')
sharp = [p.decode() for p in tracked if p.endswith(b'SHARP_ASYMPTOTIC.md')]
preferred = 'research/appt-multilevel-counterexample/SHARP_ASYMPTOTIC.md'
assert preferred in sharp, sharp
copy(REPO / preferred, 'snapshot/dependencies/SHARP_ASYMPTOTIC.md')
for alternate in sharp:
    if alternate != preferred:
        copy(REPO / alternate, 'snapshot/dependencies/preprint-copy-SHARP_ASYMPTOTIC.md')
head = subprocess.run(['git', '-C', str(REPO), 'rev-parse', 'HEAD'],
                       check=True, stdout=subprocess.PIPE).stdout.decode().strip()
manifest['repository_head_at_capture'] = head
manifest['sharp_repository_path'] = preferred
manifest['all_tracked_sharp_paths'] = sharp
(HERE / 'INPUT_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(manifest))
