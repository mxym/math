"""Capture M source and separately reviewed dependencies without changing them."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

root = Path(__file__).resolve().parent
stage = root.parent
author = stage / 'optimal-entropy-order'
old = stage / 'independent-optimal-order-review'
manifest = {'captured_utc': datetime.now(timezone.utc).isoformat(),
            'author_script_executed_by_reviewer': False,
            'math_source_changed_by_reviewer': False, 'files': {}}

def copy(source, relative):
    data = source.read_bytes()
    destination = root / relative
    if destination.exists():
        assert destination.read_bytes() == data, str(destination)
    else:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    manifest['files'][relative] = {'source': str(source),
        'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data),
        'lines': len(data.splitlines())}

for name in ['GLOBAL_ORDER.md', 'GLOBAL_TARGET.md', 'global_checks.py',
             'PAPER.md', 'THEOREM_MAP.md', 'checks.py', 'REVIEW_HISTORY.md']:
    copy(author / name, 'snapshot/M/' + name)
for name in ['REVIEW.md', 'REVIEW.json', 'PUBLISHED_INPUT_COMPARISON.json']:
    copy(old / name, 'snapshot/L-review/' + name)
copy(old / 'runs' / '20261015T081127.835786Z' / 'RESULT.json',
     'snapshot/L-review/independent-RESULT.json')
for source in (old / 'snapshot' / 'published-inputs').rglob('*'):
    if source.is_file():
        copy(source, 'snapshot/published-inputs/' +
             source.relative_to(old / 'snapshot' / 'published-inputs').as_posix())
author_run = author / 'global-control-runs' / '20261015T083026.400414Z'
for source in sorted(author_run.iterdir()):
    if source.is_file():
        copy(source, 'author-evidence/global-control-runs/' + author_run.name + '/' + source.name)
copy(author / 'control-runs' / '20261015T080542.309850Z' / 'RESULT.json',
     'author-evidence/L-constants-RESULT.json')
expected = {'GLOBAL_ORDER.md': '0b928b6c3f0b9636d6e8cb8eb0c7201f9f83c69b2b8e4d2f51b1967286875bec',
            'GLOBAL_TARGET.md': '936780ba827e3023e1bfba31eb79c0f3f023775753bebab2f4dbc5776e047eb8',
            'PAPER.md': 'c76f83bf7bb4a42eee81cafbab6fd8cdb430312fc7026503acbc86a9dfbda58b'}
for name, digest in expected.items():
    assert manifest['files']['snapshot/M/' + name]['sha256'] == digest
result = json.loads((author_run / 'RESULT.json').read_text())
assert result['status'] == 'PASS'
for name, digest in result['source_sha256'].items():
    assert manifest['files']['snapshot/M/' + name]['sha256'] == digest
    assert manifest['files']['author-evidence/global-control-runs/' + author_run.name + '/' + name]['sha256'] == digest
prior = result['groups']['constants_from_author_L_result']
assert hashlib.sha256((root / 'author-evidence/L-constants-RESULT.json').read_bytes()).hexdigest() == prior['sha256']
(root / 'INPUT_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'files': len(manifest['files']), 'source': expected, 'author_run_verified_not_reexecuted': author_run.name}))
