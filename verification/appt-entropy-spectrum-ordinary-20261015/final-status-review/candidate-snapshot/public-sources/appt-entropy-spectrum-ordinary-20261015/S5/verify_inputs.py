"""Reviewer-authored byte verification. Does not execute author code or Git."""
from pathlib import Path
import datetime as dt
import hashlib
import json

HERE = Path(__file__).resolve().parent
SRC = HERE / 'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-5-sublinear-rigidity'

def digest(p):
    b = p.read_bytes()
    return {'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}

def main():
    manifest = SRC / 'AUTHOR_V1_MANIFEST.json'
    assert digest(manifest)['sha256'] == '2d415d69e3728fb2b26f46ff9f866d067ead83efbc12b22f0fd4f1dec88586b8'
    data = json.loads(manifest.read_text())
    records = []
    for row in data['files']:
        p = SRC / Path(row['path']).name
        actual = digest(p)
        assert actual == {k: row[k] for k in ('bytes', 'sha256')}, (p, actual)
        records.append({'path': p.relative_to(HERE).as_posix(), **actual, 'role': 'owner mathematical source, metadata, author control or capture source; read, not executed'})
    source_map = json.loads((SRC / 'SOURCE_INPUTS.json').read_text())
    assert source_map['inputs'] == data['credited_inputs']
    assert len(source_map['inputs']) == 15
    for row in source_map['inputs']:
        p = SRC / 'credited-inputs' / row['path']
        actual = digest(p)
        assert actual == {k: row[k] for k in ('bytes', 'sha256')}, (p, actual)
        records.append({'path': p.relative_to(HERE).as_posix(), **actual,
                        'role': 'entire scientific text read for current proof dependencies and local range comparison; no new certification of all older theorem scopes',
                        'captured_commit': row['commit']})
    author = json.loads((SRC / 'AUTHOR_EXACT_CONTROLS.json').read_text())
    assert author['paper_sha256'] == digest(SRC / 'PAPER.md')['sha256']
    assert author['source_sha256'] == digest(SRC / 'author_exact_controls.py')['sha256']
    assert author['finite_cases'] == len(author['rows']) == 18
    assert author['all_requested_assertions_passed']
    # Prove that no files have been silently added to the archive after capture.
    archive_files = sorted(p.relative_to(SRC).as_posix() for p in SRC.rglob('*') if p.is_file())
    expected = sorted([Path(x['path']).name for x in data['files']] + ['AUTHOR_V1_MANIFEST.json'] + ['credited-inputs/' + x['path'] for x in data['credited_inputs']])
    assert archive_files == expected, (archive_files, expected)
    result = {'status': 'PASS', 'decision': 'PASS', 'time_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
              'manifest': digest(manifest), 'owner_zip': digest(HERE / 'owner.zip'),
              'captured_source_base': source_map['root_capture_commit'],
              'archive_files': len(archive_files), 'verified_manifest_files': len(data['files']),
              'verified_credited_inputs': len(source_map['inputs']),
              'author_controls': {'read_only': True, 'executed_by_reviewer': False, 'reported_cases': 18,
                                  'stored_utc_unchanged': author['utc']},
              'records': records,
              'not_performed': ['Git operations', 'author control execution', 'Lean', 'publication', 'priority certification']}
    return result

if __name__ == '__main__':
    value = main()
    target = HERE / 'INPUT_VERIFICATION.json'
    assert not target.exists(), 'Do not overwrite a previous verification run.'
    target.write_text(json.dumps(value, indent=2) + '\n')
    print(json.dumps({k: v for k, v in value.items() if k != 'records'}, indent=2))
