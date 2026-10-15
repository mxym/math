"""New independent byte/navigation checker; does not execute mathematical controls."""
from pathlib import Path, PurePosixPath
from collections import Counter
import datetime as dt
import difflib
import hashlib
import json
import posixpath
import re
import subprocess
import unicodedata

HERE = Path(__file__).resolve().parent
SNAP = HERE/'candidate-snapshot'
STAGE = HERE.parent/'phase-diagram-publication'
INPUTS = HERE/'stage-inputs'
BASE = '1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
ROOT = '/home/mxym/math-appt-multiscale-20261013'
OWNER = '/home/mxym/math-breadth-tcs-20261015'
RESEARCH = 'research/appt-linear-phase-diagram-20261015'
EVIDENCE = 'verification/appt-linear-phase-diagram-ordinary-20261015'

def sha(data): return hashlib.sha256(data).hexdigest()
def digest(path):
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': sha(data)}

def objects(repo, requests):
    proc = subprocess.run(['git', '-C', repo, 'cat-file', '--batch'],
                          input=('\n'.join(requests)+'\n').encode(), capture_output=True, check=True)
    result = {}
    pos = 0
    for request in requests:
        end = proc.stdout.index(b'\n', pos)
        head = proc.stdout[pos:end].decode().split()
        assert len(head) == 3 and head[1] == 'blob', (request, head)
        length = int(head[2])
        data = proc.stdout[end+1:end+1+length]
        assert len(data) == length and proc.stdout[end+1+length:end+2+length] == b'\n'
        assert hashlib.sha1(b'blob '+str(length).encode()+b'\0'+data).hexdigest() == head[0]
        result[request] = (head[0], data)
        pos = end+2+length
    assert pos == len(proc.stdout)
    return result

def links(text):
    return re.findall(r'\]\(([^\n]+?)\)', text)

def anchors(text):
    results = set()
    repeated = Counter()
    fence = None
    for line in text.splitlines():
        mark = re.match(r'^\s*(```+|~~~+)', line)
        if mark:
            fence = None if fence else mark[1][0]
            continue
        if fence:
            continue
        match = re.match(r'^#{1,6}\s+(.+?)\s*#*$', line)
        if not match:
            continue
        title = re.sub(r'\[([^\]]+)\]\([^)]*\)', r'\1', match[1])
        title = re.sub(r'<[^>]+>', '', title).replace('`', '').replace('*', '').lower()
        slug = ''.join(c for c in title if c in '_-' or c.isspace() or unicodedata.category(c)[0] in 'LNM')
        slug = re.sub(r'\s+', '-', slug.strip())
        index = repeated[slug]
        repeated[slug] += 1
        results.add(slug if index == 0 else slug+'-'+str(index))
    results.update(re.findall(r'\bid=["\']([^"\']+)["\']', text))
    return results

def main():
    manifest = json.loads((INPUTS/'FINAL_CANDIDATE_INPUTS.json').read_text())
    assert manifest['source_base'] == BASE and len(manifest['files']) == 248
    assert sha((STAGE/'FINAL_CANDIDATE_INPUTS.json').read_bytes()) == sha((INPUTS/'FINAL_CANDIDATE_INPUTS.json').read_bytes())
    bound = {}
    for rel, expected in manifest['files'].items():
        data = (SNAP/rel).read_bytes()
        assert sha(data) == expected
        if rel in ('README.md', 'README.en.md', 'RESEARCH.md'):
            current = STAGE/'index-candidates'/rel
        else:
            name, dest = next((name, dest) for name, dest in manifest['new_projects'].items() if rel.startswith(dest+'/'))
            current = STAGE/'public-sources'/name/rel[len(dest)+1:]
        assert current.read_bytes() == data, rel
        bound[rel] = {'sha256': expected, 'bytes': len(data)}
    index = json.loads((INPUTS/'index-candidates/INDEX_BINDINGS.json').read_text())
    before = objects(ROOT, [BASE+':'+rel for rel in index])
    changes = {}
    for rel, declared in index.items():
        oid, old = before[BASE+':'+rel]
        new = (SNAP/rel).read_bytes()
        assert old == (HERE/'base-inputs'/rel).read_bytes()
        assert sha(old) == declared['before_sha256'] and sha(new) == declared['after_sha256']
        a, b = old.splitlines(keepends=True), new.splitlines(keepends=True)
        assert len(a) == len(b)
        positions = [i for i, (x, y) in enumerate(zip(a, b)) if x != y]
        assert len(positions) == 1
        i = positions[0]
        assert b'appt-linear-phase-geometry-20261015/README.md' in a[i]
        assert b'appt-linear-phase-geometry-20261015/README.md' in b[i]
        assert b'appt-linear-phase-diagram-20261015/README.md' in b[i]
        assert not (Counter(links(old.decode()))-Counter(links(new.decode())))
        exact_diff = ''.join(difflib.unified_diff(old.decode().splitlines(True), new.decode().splitlines(True),
                                                fromfile='before/'+rel, tofile='candidate/'+rel)).encode()
        assert exact_diff == (INPUTS/(rel.replace('.', '_')+'.candidate.diff')).read_bytes()
        changes[rel] = {'changed_line': i+1, 'base_git_blob': oid, **declared,
                        'before_row': a[i].decode().rstrip(), 'after_row': b[i].decode().rstrip(),
                        'all_other_lines_exact': True, 'all_old_url_occurrences_retained': True}
    owner = json.loads((SNAP/RESEARCH/'OWNER_SOURCE_BINDINGS.json').read_text())
    assert len(owner['files']) == 50
    requested = [owner['source_commit']+':'+owner['source_prefix']+rel for rel in owner['files']]
    actual = objects(OWNER, requested)
    for rel, row in owner['files'].items():
        key = owner['source_commit']+':'+owner['source_prefix']+rel
        oid, data = actual[key]
        assert oid == row['git_blob'] and sha(data) == row['sha256'] and len(data) == row['bytes']
        assert data == (SNAP/RESEARCH/'author-snapshot'/rel).read_bytes()
    frozen = HERE.parent/'independent-critical-boundary-review-20261015'
    copied = SNAP/EVIDENCE/'independent-source'
    all_old = {p.relative_to(frozen).as_posix(): digest(p) for p in frozen.rglob('*') if p.is_file()}
    excluded = {rel: info for rel, info in all_old.items() if '__pycache__' in PurePosixPath(rel).parts and rel.endswith('.pyc')}
    assert len(excluded) == 15
    durable = {rel: info for rel, info in all_old.items() if rel not in excluded}
    public = {p.relative_to(copied).as_posix(): digest(p) for p in copied.rglob('*') if p.is_file()}
    assert len(durable) == len(public) == 186 and durable == public
    scopes = json.loads((copied/'FOUR_SCOPE_REPORT_BINDINGS.json').read_text())
    assert scopes['status'] == scopes['decision'] == 'PASS' and len(scopes['scopes']) == 4
    for row in scopes['scopes']:
        assert row['decision'] == 'PASS'
        for key in ('review_md', 'review_json'):
            assert digest(copied/row[key]['path']) == {k: row[key][k] for k in ('bytes', 'sha256')}
    for key, project_file in [('combined_md', 'REVIEW.md'), ('combined_json', 'REVIEW.json')]:
        row = scopes[key]
        assert (SNAP/RESEARCH/project_file).read_bytes() == (copied/row['path']).read_bytes()
        assert digest(copied/row['path']) == {k: row[k] for k in ('bytes', 'sha256')}
    expected_math = json.loads((INPUTS/'PREPARED_CANDIDATES.json').read_text())['four_math_sources']
    assert set(expected_math.values()) == {row['source_sha256'] for row in scopes['scopes']}
    for rel, expected in expected_math.items():
        assert digest(SNAP/RESEARCH/'author-snapshot'/rel)['sha256'] == expected
    # Navigation paths are checked against immutable base blobs and staged files,
    # including real staged directory targets; no working-tree source is used.
    raw_tree = subprocess.check_output(['git', '-C', ROOT, 'ls-tree', '-r', '--name-only', '-z', BASE])
    tracked = set(raw_tree.decode().rstrip('\0').split('\0'))
    known = set(bound) | tracked
    canonical = list(index)+[RESEARCH+'/README.md', RESEARCH+'/STATUS.md', EVIDENCE+'/README.md']
    checked, pending, fragments = [], [], []
    for rel in canonical:
        for link in links((SNAP/rel).read_text()):
            if '://' in link or link.startswith('mailto:'):
                continue
            path, sep, fragment = link.strip('<>').partition('#')
            target = posixpath.normpath(posixpath.join(posixpath.dirname(rel), path)) if path else rel
            assert not target.startswith(('/', '../')), (rel, link)
            if target == RESEARCH+'/FINAL_STATUS_BINDING.json':
                pending.append({'source': rel, 'target': target, 'scope': 'This same final binding is to be installed/read back separately; no future transport guarantee.'})
                continue
            assert target in known or any(x.startswith(target.rstrip('/')+'/') for x in known), (rel, link, target)
            if path:
                checked.append({'source': rel, 'target': target})
            if sep and fragment:
                if target in bound:
                    text = (SNAP/target).read_text()
                else:
                    text = objects(ROOT, [BASE+':'+target])[BASE+':'+target][1].decode()
                assert fragment in anchors(text), (rel, link, target, sorted(anchors(text)))
                fragments.append({'source': rel, 'target': target, 'fragment': fragment})
    assert len(checked) == 426 and len(pending) == 1 and len(fragments) == 22
    result = {'status': 'PASS', 'decision': 'PASS', 'utc': dt.datetime.now(dt.timezone.utc).isoformat(),
              'input_manifest': digest(INPUTS/'FINAL_CANDIDATE_INPUTS.json'), 'source_base': BASE,
              'candidate_files': bound, 'owner_immutable_git_files_verified': 50,
              'owner_source_commit': owner['source_commit'], 'four_math_sources_unchanged': expected_math,
              'four_separate_math_reports': scopes['scopes'], 'three_index_changes': changes,
              'independent_source_durable_exact': 186, 'excluded_private_interpreter_caches': excluded,
              'navigation_checked_paths': len(checked), 'navigation_fragments_checked': len(fragments),
              'pending_self_binding_installation': pending, 'navigation': checked, 'fragments': fragments,
              'current_candidate_bytes_unchanged': True,
              'no_mathematics_controls_author_code_Lean_or_Git_mutation_executed': True}
    return result

if __name__ == '__main__':
    run = HERE/'metadata-runs'/dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    run.mkdir(parents=True)
    (run/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    try:
        value = main()
    except Exception:
        import traceback
        value = {'status': 'FAIL', 'utc': dt.datetime.now(dt.timezone.utc).isoformat(), 'traceback': traceback.format_exc()}
        (run/'RESULT.json').write_text(json.dumps(value, indent=2)+'\n')
        raise
    (run/'RESULT.json').write_text(json.dumps(value, indent=2)+'\n')
    print(json.dumps({'run': str(run), 'status': value['status'], 'candidate_files': len(value['candidate_files']),
                      'owner_files': value['owner_immutable_git_files_verified'],
                      'durable_independent_files': value['independent_source_durable_exact'],
                      'excluded_caches': len(value['excluded_private_interpreter_caches']),
                      'canonical_paths': value['navigation_checked_paths'], 'fragments': value['navigation_fragments_checked']}, indent=2))
