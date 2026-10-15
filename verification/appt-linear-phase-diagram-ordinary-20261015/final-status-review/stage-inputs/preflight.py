"""Read-only source/navigation preflight; the only writes are its private receipts."""
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
from collections import Counter
import difflib, hashlib, json, posixpath, re, subprocess

stage = Path(__file__).resolve().parent
root = Path('/home/mxym/math-appt-multiscale-20261013')
public = stage / 'public-sources'
prepared = json.loads((stage / 'PREPARED_CANDIDATES.json').read_text())
base = prepared['source_base']

def git(*args):
    return subprocess.check_output(['git', '-C', str(root), *args])

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert git('rev-parse', 'HEAD').decode().strip() == base
assert not git('status', '--porcelain').strip(), 'Preserve unexpected root changes first'
projects = {p.name: ('verification/' if p.name.endswith('ordinary-20261015') else 'research/') + p.name
            for p in sorted(public.iterdir()) if p.is_dir()}
assert len(projects) == 2
files, lookup = {}, {}
for name, dest in projects.items():
    for p in sorted((public / name).rglob('*')):
        if not p.is_file():
            continue
        rel = dest + '/' + p.relative_to(public / name).as_posix()
        files[rel], lookup[rel] = sha(p), p
index = json.loads((stage / 'index-candidates' / 'INDEX_BINDINGS.json').read_text())
assert set(index) == {'README.md', 'README.en.md', 'RESEARCH.md'}
index_changes = {}
def urls(text):
    return Counter(re.findall(r'\]\(([^\n]+?)\)', text))

for name, binding in index.items():
    before = root / name
    after = stage / 'index-candidates' / name
    assert sha(before) == binding['before_sha256']
    assert sha(after) == binding['after_sha256']
    old, new = before.read_text(), after.read_text()
    a, b = old.splitlines(True), new.splitlines(True)
    assert len(a) == len(b)
    different = [i for i, (x, y) in enumerate(zip(a, b)) if x != y]
    assert len(different) == 1, (name, different)
    i = different[0]
    assert a[i].startswith('| ') and b[i].startswith('| ')
    assert 'appt-linear-phase-geometry-20261015/README.md' in a[i]
    assert 'appt-linear-phase-geometry-20261015/README.md' in b[i]
    assert 'appt-linear-phase-diagram-20261015/README.md' in b[i]
    assert not (urls(old) - urls(new)), (name, 'An existing link was removed')
    assert not re.search(r'^#{1,6}\s+已宣称解决的问题\s*$', new, re.M)
    assert not re.search(r'^#{1,6}\s+Claimed solved problems\s*$', new, re.M | re.I)
    files[name], lookup[name] = sha(after), after
    index_changes[name] = {'changed_line': i+1, 'only_existing_phase_row_replaced': True,
                           'all_other_lines_literal_preserved': True,
                           'all_previous_link_occurrences_preserved': True}
    (stage / (name.replace('.', '_') + '.candidate.diff')).write_text(''.join(
        difflib.unified_diff(a, b, fromfile='before/'+name, tofile='candidate/'+name)))

project = public / 'appt-linear-phase-diagram-20261015'
evidence = public / 'appt-linear-phase-diagram-ordinary-20261015'
owner = json.loads((project / 'OWNER_SOURCE_BINDINGS.json').read_text())
assert len(owner['files']) == 50
for rel, v in owner['files'].items():
    p = project / 'author-snapshot' / rel
    assert sha(p) == v['sha256'] and p.stat().st_size == v['bytes']
    source_rel = owner['source_prefix'] + rel
    assert p.read_bytes() == git('show', owner['source_commit']+':'+source_rel)
    assert v['git_blob'] == git('rev-parse', owner['source_commit']+':'+source_rel).decode().strip()
for rel, h in prepared['four_math_sources'].items():
    assert sha(project / 'author-snapshot' / rel) == h
frozen_review = stage.parent / 'independent-critical-boundary-review-20261015'
for rel in ('COMBINED_REVIEW_FOUR.md', 'COMBINED_REVIEW_FOUR.json'):
    assert (evidence / 'independent-source' / rel).read_bytes() == (frozen_review / rel).read_bytes()
assert (project / 'REVIEW.md').read_bytes() == (frozen_review / 'COMBINED_REVIEW_FOUR.md').read_bytes()
assert (project / 'REVIEW.json').read_bytes() == (frozen_review / 'COMBINED_REVIEW_FOUR.json').read_bytes()
scope = json.loads((frozen_review / 'FOUR_SCOPE_REPORT_BINDINGS.json').read_text())
assert scope['status'] == scope['decision'] == 'PASS' and len(scope['scopes']) == 4
for s in scope['scopes']:
    assert s['decision'] == 'PASS'
    for key in ('review_md', 'review_json'):
        assert sha(frozen_review / s[key]['path']) == s[key]['sha256']

# Historical author/reviewer snapshots keep their original relative contexts.
# Verify the current navigation documents in their proposed publication paths.
canonical = list(index) + [projects[project.name]+'/README.md',
                          projects[project.name]+'/STATUS.md',
                          projects[evidence.name]+'/README.md']
checked, pending = [], []
for rel in canonical:
    text = lookup[rel].read_text()
    for link in re.findall(r'\]\(([^\n]+?)\)', text):
        if '://' in link or link.startswith(('#', 'mailto:')):
            continue
        target = link.split('#', 1)[0].strip('<>')
        if not target:
            continue
        resolved = posixpath.normpath(posixpath.join(posixpath.dirname(rel), target))
        assert not resolved.startswith('../') and not resolved.startswith('/'), (rel, link)
        if resolved.endswith('/FINAL_STATUS_BINDING.json'):
            pending.append({'source': rel, 'target': resolved})
        elif resolved in lookup or any(p.startswith(resolved.rstrip('/')+'/') for p in lookup) or (root / resolved).exists():
            checked.append({'source': rel, 'target': resolved})
        else:
            raise AssertionError(('Missing canonical link', rel, link, resolved))

receipt = {'utc': datetime.now(timezone.utc).isoformat(), 'status': 'PASS',
           'purpose': 'Exact source/status/navigation preparation only; not a mathematical or formal review',
           'source_base': base, 'new_projects': projects,
           'frozen_author_files_checked': 50, 'separate_math_reports_verified': 4,
           'index_changes': index_changes, 'canonical_links_checked': len(checked),
           'pending_final_binding_links': pending, 'new_Lean': False, 'new_major_count': 0,
           'files': files}
(stage / 'FINAL_CANDIDATE_INPUTS.json').write_text(json.dumps(receipt, indent=2)+'\n')
(stage / 'CANONICAL_LINKS.json').write_text(json.dumps(checked, indent=2)+'\n')
print(json.dumps({'status': 'PASS', 'source_base': base, 'bound_files': len(files),
                  'canonical_links_checked': len(checked), 'index_changes': 3,
                  'frozen_author_files': 50, 'separate_math_reports': 4}))
