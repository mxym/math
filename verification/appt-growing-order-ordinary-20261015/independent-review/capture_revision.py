"""Capture corrected P2, preserving the original rejected-range source."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, difflib

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / 'growing-renyi-order'
manifest = json.loads((HERE / 'INPUT_MANIFEST.json').read_text())
original_manifest = HERE / 'history' / 'initial-INPUT_MANIFEST.json'
if not original_manifest.exists():
    original_manifest.write_bytes((HERE / 'INPUT_MANIFEST.json').read_bytes())

def copy(source, destination):
    data = source.read_bytes(); target = HERE / destination
    if target.exists():
        assert target.read_bytes() == data, str(target)
    else:
        target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
    manifest['files'][destination] = {'source': str(source),
        'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data),
        'lines': len(data.splitlines())}

for name in ['PAPER.md', 'THEOREM_MAP.md', 'REVIEW_HISTORY.md', 'checks.py']:
    copy(AUTHOR / name, 'snapshot/P-v2/' + name)
for name in ['PAPER.md', 'THEOREM_MAP.md', 'checks.py']:
    prior = AUTHOR / 'author-versions' / 'before-fixed-dimension-quantifier-fix' / name
    copy(prior, 'author-versions/before-fixed-dimension-quantifier-fix/' + name)
    if name != 'checks.py':
        assert prior.read_bytes() == (HERE / 'snapshot' / 'P' / name).read_bytes()
for folder in sorted((AUTHOR / 'control-runs').iterdir()):
    if folder.is_dir():
        for source in sorted(folder.iterdir()):
            if source.is_file():
                copy(source, 'author-evidence/' + folder.name + '/' + source.name)
        data = json.loads((folder / 'RESULT.json').read_text())
        assert data['status'] == 'PASS'
        for name, value in data['source_sha256'].items():
            assert hashlib.sha256((folder / name).read_bytes()).hexdigest() == value
for name in ['PAPER.md', 'THEOREM_MAP.md']:
    old = (HERE / 'snapshot' / 'P' / name).read_text().splitlines(True)
    new = (HERE / 'snapshot' / 'P-v2' / name).read_text().splitlines(True)
    difference = ''.join(difflib.unified_diff(old, new, fromfile='original/' + name,
                                            tofile='corrected/' + name))
    output = HERE / 'history' / (name + '.diff')
    output.write_text(difference)
manifest['corrected_source_captured_utc'] = datetime.now(timezone.utc).isoformat()
assert manifest['files']['snapshot/P-v2/PAPER.md']['sha256'] == '50d2092695d687b526f7d52dccaba05bfb9926bf8f8beb3bb94c29a68164428c'
(HERE / 'INPUT_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'corrected': {name: manifest['files']['snapshot/P-v2/' + name]
                   for name in ['PAPER.md', 'THEOREM_MAP.md', 'REVIEW_HISTORY.md', 'checks.py']},
                   'total_files': len(manifest['files']), 'author_controls_executed': False}))
