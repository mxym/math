"""Metadata/source binding only. No mathematical or author control is run."""
from pathlib import Path
from datetime import datetime, timezone
import difflib, hashlib, json, re, subprocess

HERE = Path(__file__).resolve().parent
STAGE = HERE.parent
PUB = STAGE / 'optimal-order-publication'
CANDIDATE = PUB / 'public-sources' / 'appt-optimal-entropy-order-20261015'
INDEX = PUB / 'index-candidates'
BASE = '5522928ae7e8b1960dedb790d7f3506f3b1f5f0b'
GIT = '/home/mxym/math-appt-multiscale-20261013'
manifest = {'captured_utc': datetime.now(timezone.utc).isoformat(),
            'no_mathematical_controls_executed': True, 'files': {}}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def put(relative, data, source):
    dest = HERE / relative
    if dest.exists():
        assert dest.read_bytes() == data, str(dest)
    else:
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
    record = {'sha256': digest(data), 'bytes': len(data), 'lines': len(data.splitlines()),
              'source': source}
    manifest['files'][relative] = record
    return record

# Retain the initially inspected README and records before the author adopts
# two metadata clarifications. Never rewrite either prior mathematical source.
previous_readme = HERE / 'snapshot' / 'candidate' / 'README.md'
if previous_readme.exists() and previous_readme.read_bytes() != (CANDIDATE / 'README.md').read_bytes():
    prior = previous_readme.read_bytes()
    author_prior = CANDIDATE / 'author-versions' / 'publication-metadata-v1' / 'README.md'
    assert author_prior.read_bytes() == prior
    put('history/publication-metadata-v1/README.md', prior, 'initially inspected candidate README')
    for name in ['INPUT_MANIFEST.json', 'BYTE_CHECKS.json']:
        source = HERE / name
        put('history/publication-metadata-v1/' + name, source.read_bytes(), str(source))
    difference = ''.join(difflib.unified_diff(prior.decode().splitlines(keepends=True),
        (CANDIDATE / 'README.md').read_text().splitlines(keepends=True),
        fromfile='initial-metadata/README.md', tofile='clarified-metadata/README.md'))
    put('history/publication-metadata-v1/README-clarifications.diff', difference.encode(),
        'complete diff for two metadata clarifications')
    previous_readme.write_bytes((CANDIDATE / 'README.md').read_bytes())

for p in sorted(CANDIDATE.rglob('*')):
    if p.is_file() and p.name != 'FINAL_STATUS_BINDING.json':
        relative = p.relative_to(CANDIDATE).as_posix()
        put('snapshot/candidate/' + relative, p.read_bytes(), str(p))
for p in sorted(INDEX.iterdir()):
    if p.is_file():
        put('snapshot/index/' + p.name, p.read_bytes(), str(p))
put('snapshot/FINAL_SOURCE_CANDIDATES.json', (PUB / 'FINAL_SOURCE_CANDIDATES.json').read_bytes(),
    str(PUB / 'FINAL_SOURCE_CANDIDATES.json'))

def reverse_status(final, patch):
    """Apply exact unified-diff inverse; refuse every mismatched context byte."""
    lines = final.splitlines(keepends=True)
    changes = patch.splitlines(keepends=True)
    assert changes[0].startswith(b'--- ') and changes[1].startswith(b'+++ ')
    pos, i, output, hunks = 0, 2, [], []
    while i < len(changes):
        match = re.fullmatch(rb'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*\n', changes[i])
        assert match, changes[i]
        oldstart = int(match[1]); oldcount = int(match[2] or b'1')
        newstart = int(match[3]); newcount = int(match[4] or b'1')
        start = newstart - 1
        assert pos <= start
        output.extend(lines[pos:start]); pos = start; i += 1
        oldseen, newseen = 0, 0
        while i < len(changes) and not changes[i].startswith(b'@@ '):
            line = changes[i]; prefix, payload = line[:1], line[1:]
            assert prefix in (b' ', b'-', b'+'), line
            if prefix in (b' ', b'+'):
                assert lines[pos] == payload, (pos, lines[pos], payload)
                pos += 1; newseen += 1
            if prefix in (b' ', b'-'):
                output.append(payload); oldseen += 1
            i += 1
        assert (oldseen, newseen) == (oldcount, newcount)
        hunks.append({'old_start': oldstart, 'old_count': oldcount,
                      'new_start': newstart, 'new_count': newcount})
    output.extend(lines[pos:])
    return b''.join(output), hunks

math = {}
specs = {
    'L': {'paper': 'PAPER.md', 'diff': 'L_FINAL_STATUS.diff',
          'old': STAGE / 'independent-optimal-order-review' / 'snapshot' / 'L' / 'PAPER.md',
          'review': STAGE / 'independent-optimal-order-review',
          'reviewed_sha': 'c76f83bf7bb4a42eee81cafbab6fd8cdb430312fc7026503acbc86a9dfbda58b',
          'final_sha': '931a62d45ba66651eee849c1c7f1eef53382cb5e9993e6dea19fdb55018a9655'},
    'M': {'paper': 'GLOBAL_ORDER.md', 'diff': 'M_FINAL_STATUS.diff',
          'old': STAGE / 'independent-global-order-review' / 'snapshot' / 'M' / 'GLOBAL_ORDER.md',
          'review': STAGE / 'independent-global-order-review',
          'reviewed_sha': '0b928b6c3f0b9636d6e8cb8eb0c7201f9f83c69b2b8e4d2f51b1967286875bec',
          'final_sha': '8f60a418dd0f6ffc72f3aaa71ad6a1c1bc238c0ccb674dd636499b136532fed2'}
}
author_manifest = json.loads((PUB / 'FINAL_SOURCE_CANDIDATES.json').read_text())
assembled = json.loads((CANDIDATE / 'REVIEW.json').read_text())
assert assembled['kind'] == 'root-assembled index of literal independent reports'
assert assembled['targets'] == ['L0-L2', 'M0-M2']
for key, spec in specs.items():
    final = (CANDIDATE / spec['paper']).read_bytes()
    patch = (CANDIDATE / spec['diff']).read_bytes()
    reviewed = spec['old'].read_bytes()
    restored, hunks = reverse_status(final, patch)
    assert restored == reviewed
    assert digest(restored) == spec['reviewed_sha']
    assert digest(final) == spec['final_sha']
    assert len(hunks) == 2
    item = author_manifest[key]
    assert item['reviewed_sha256'] == digest(restored)
    assert item['final_sha256'] == digest(final)
    assert item['status_diff_sha256'] == digest(patch)
    assert item['mathematical_edits'] is False
    # Regenerating the complete forward diff must reproduce the supplied patch bytes.
    diff_text = ''.join(difflib.unified_diff(reviewed.decode().splitlines(keepends=True),
        final.decode().splitlines(keepends=True),
        fromfile=patch.splitlines()[0][4:].decode(), tofile=patch.splitlines()[1][4:].decode()))
    assert diff_text.encode() == patch
    put('reconstructed/' + key + '-' + spec['paper'], restored, 'exact inverse of candidate status diff')
    report_md = (spec['review'] / 'REVIEW.md').read_bytes()
    report_json = (spec['review'] / 'REVIEW.json').read_bytes()
    assert (CANDIDATE / (key + '_REVIEW.md')).read_bytes() == report_md
    assert (CANDIDATE / (key + '_REVIEW.json')).read_bytes() == report_json
    assert assembled['independent_reports'][key]['report_sha256'] == digest(report_md)
    assert assembled['independent_reports'][key]['binding_sha256'] == digest(report_json)
    math[key] = {'reviewed_sha256': digest(restored), 'final_sha256': digest(final),
        'diff_sha256': digest(patch), 'inverse_exact': True, 'complete_diff_exact': True,
        'hunks': hunks, 'mathematical_changes': False,
        'literal_report_sha256': digest(report_md), 'literal_record_sha256': digest(report_json)}

# Unchanged maps, scalar scripts and reviewer-contribution history.
frozen_l = STAGE / 'independent-optimal-order-review' / 'snapshot' / 'L'
frozen_m = STAGE / 'independent-global-order-review' / 'snapshot' / 'M'
for name in ['THEOREM_MAP.md', 'checks.py', 'REVIEW_HISTORY.md']:
    assert (CANDIDATE / name).read_bytes() == (frozen_l / name).read_bytes()
for name in ['GLOBAL_TARGET.md', 'global_checks.py']:
    assert (CANDIDATE / name).read_bytes() == (frozen_m / name).read_bytes()

# Direct immutable-commit comparison: each index changes by exactly its one supplied row.
bindings = json.loads((INDEX / 'INDEX_BINDINGS.json').read_text())
rows_document = (INDEX / 'ADDED_ROWS.md').read_text()
indices = {}
for name in ['README.md', 'README.en.md', 'RESEARCH.md']:
    completed = subprocess.run(['git', '-C', GIT, 'show', BASE + ':' + name],
                               check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    base = completed.stdout; after = (INDEX / name).read_bytes()
    put('snapshot/base-5522928/' + name, base, 'git show ' + BASE + ':' + name)
    needled = [line for line in after.splitlines(keepends=True)
               if b'research/appt-optimal-entropy-order-20261015/README.md' in line]
    assert len(needled) == 1
    row = needled[0]
    assert after.count(row) == 1 and after.replace(row, b'', 1) == base
    assert row.decode().strip() in rows_document
    assert bindings[name]['before_sha256'] == digest(base)
    assert bindings[name]['after_sha256'] == digest(after)
    assert bindings[name]['added_rows'] == 1
    diff = ''.join(difflib.unified_diff(base.decode().splitlines(keepends=True),
        after.decode().splitlines(keepends=True), fromfile=BASE + '/' + name, tofile='candidate/' + name))
    put('index-diffs/' + name + '.diff', diff.encode(), 'complete computed index difference')
    indices[name] = {'base_commit': BASE, 'before_sha256': digest(base),
                     'after_sha256': digest(after), 'only_added_rows': 1,
                     'all_old_bytes_preserved': True, 'added_row': row.decode().rstrip('\n')}

verification = {'checked_utc': datetime.now(timezone.utc).isoformat(),
    'math_source_relations': math, 'index_relations': indices,
    'literal_independent_reports_unchanged': True,
    'root_assembled_index_is_not_new_independent_report': True,
    'no_mathematical_controls_executed': True, 'no_Lean_executed': True,
    'future_evidence_layout_verified': False,
    'future_evidence_reference': 'verification/appt-optimal-order-ordinary-20261015/README.md'}
(HERE / 'INPUT_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
(HERE / 'BYTE_CHECKS.json').write_text(json.dumps(verification, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'snapshot_files': len(manifest['files']),
                  'inverse_exact': list(math), 'indices_one_row_only': list(indices),
                  'future_layout_certified': False}))
