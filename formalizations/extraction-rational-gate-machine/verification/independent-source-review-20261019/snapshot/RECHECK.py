"""Read-only Git/source/actual author-log recheck. Never starts Lean or a build."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parent
FIXED = {'fifths': '72f9b28bd31887b320d08b5b10c78b7299d45168',
         'query': 'f8361330f09e3201cc45337efacf6957f937ad29'}
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}


def unique(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError('Duplicate JSON key: ' + key)
        out[key] = value
    return out


def readj(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def local(name):
    if not isinstance(name, str) or not name or '\\' in name or ':' in name:
        raise ValueError('Unsafe local name')
    pure = PurePosixPath(name)
    if pure.is_absolute() or '..' in pure.parts or pure.as_posix() != name:
        raise ValueError('Unsafe relative path')
    result = ROOT.joinpath(*pure.parts)
    if any(p.is_symlink() for p in [result, *result.parents] if p.is_relative_to(ROOT)):
        raise ValueError('Symlink in evidence')
    return result


def file_manifest():
    return {p.relative_to(ROOT).as_posix(): sha(p.read_bytes()) for p in sorted(ROOT.rglob('*'))
            if p.is_file() and p != ROOT / 'EVIDENCE_HASHES.json'}


def actual_axioms(text):
    result = {}
    for match in re.finditer(r"'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", text):
        if match[1] in result:
            raise ValueError('Duplicate axiom observation')
        values = [] if match[2] is None else [x.strip() for x in match[2].split(',') if x.strip()]
        if len(values) != len(set(values)) or set(values) - ALLOW:
            raise ValueError('Unexpected actual axiom list')
        result[match[1]] = values
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', default='/home/mxym/math-extraction-lean-minimax-20261016')
    parser.add_argument('--snapshots-only', action='store_true',
                        help='Do not reopen the original D author logs; copied log bytes still match the fixed Git reports.')
    args = parser.parse_args()
    if readj(ROOT / 'EVIDENCE_HASHES.json') != file_manifest():
        raise ValueError('Review evidence bytes changed')
    sources = readj(ROOT / 'GIT_SNAPSHOT_MANIFEST.json')
    if set(sources) != set(FIXED):
        raise ValueError('Changed fixed review targets')
    blob_count = 0
    for key, rev in FIXED.items():
        if sources[key]['commit'] != rev:
            raise ValueError('Wrong fixed Git commit')
        for name, row in sources[key]['files'].items():
            expected = 'snapshot/' + key + '/' + name
            if row['snapshot'] != expected:
                raise ValueError('Wrong Git snapshot path')
            data = local(expected).read_bytes()
            oid = subprocess.check_output(['git', '-C', args.repo, 'rev-parse', rev + ':' + name], text=True).strip()
            git_bytes = subprocess.check_output(['git', '-C', args.repo, 'cat-file', 'blob', oid])
            if oid != row['git_blob'] or data != git_bytes or sha(data) != row['sha256'] or len(data) != row['bytes']:
                raise ValueError('Fixed Git blob differs: ' + name)
            blob_count += 1
    logs = readj(ROOT / 'ACTUAL_LOGS_MANIFEST.json')
    if len(logs) != 6:
        raise ValueError('Wrong actual log inventory')
    for name, row in logs.items():
        if row['snapshot'] != 'logs/' + name:
            raise ValueError('Wrong log snapshot path')
        data = local(row['snapshot']).read_bytes()
        if sha(data) != row['sha256'] or len(data) != row['bytes']:
            raise ValueError('Copied author log differs')
        author = readj(local(row['author_report']))
        if author.get('logs', {}).get(name, author.get('check_log_sha256')) != row['sha256']:
            raise ValueError('Log SHA differs from fixed Git author report')
        if not args.snapshots_only:
            original = Path(row['original'])
            if original.parent != Path('/mnt/d/math/tmp/extraction-resume-20261018/build-logs') or original.name != name:
                raise ValueError('Unexpected original log location')
            if original.read_bytes() != data:
                raise ValueError('Original actual author log changed')
    declarations = readj(ROOT / 'DECLARATIONS_AND_ACTUAL_AXIOMS.json')
    for key, counts, logname in [
        ('fifths', (26, 11), '20261019T000758259036Z-root-owned-RationalGateMachine.BinaryFifthsCheck.log'),
        ('query', (58, 40), '20261019T002525789091Z-owned-check-CircuitNumerical.NativeQueryCheck.log')]:
        item = declarations[key]
        if item['commit'] != FIXED[key] or (len(item['theorems']), len(item['models'])) != counts:
            raise ValueError('Wrong declaration roots')
        log = local('logs/' + logname).read_text()
        if actual_axioms(log) != item['actual_axioms']:
            raise ValueError('Actual multiline/empty axiom observation differs')
        wanted = item['theorems'] + item['models'] if key == 'fifths' else item['theorems']
        if set(item['actual_axioms']) != set(wanted):
            raise ValueError('Incomplete actual axiom observations')
        for name in item['theorems'] + item['models']:
            if len(re.findall(r'^' + re.escape(name) + r'(?=\.\{|\s|:)', log, re.M)) != 1:
                raise ValueError('Missing/duplicate actual type header')
            row = item['declarations'][name]
            source = local(sources[key]['files'][row['path']]['snapshot'])
            if sha(source.read_bytes()) != row['source_sha256']:
                raise ValueError('Declaration source hash differs')
        if item['environment_kind_checks'] != (key == 'fifths') or item['independent_kernel'] is not False:
            raise ValueError('Wrong evidence strength')
    if local('logs/20261019T000758259036Z-root-owned-RationalGateMachine.BinaryFifthsCheck.log').read_text().count('FINITE_TM2_BINARY_FIFTHS_165_ACTUAL_RUNS_PASS') != 1:
        raise ValueError('Missing original actual 165-run result')
    for name, jobs in [('20261019T000806861490Z-extraction-rational-gate-machine.log', 4002),
                       ('20261019T002551035911Z-extraction-numerical-synthesis.log', 4028)]:
        if f'Build completed successfully ({jobs} jobs).' not in local('logs/' + name).read_text():
            raise ValueError('Missing actual aggregate build result')
    report = readj(ROOT / 'REPORT.json')
    if report['status'] != 'INDEPENDENT_SOURCE_AND_EXISTING_LOG_REVIEW_NO_SUBSTANTIVE_DEFECT_FOUND_NOT_NEW_KERNEL' or report['lean_invocations'] != 0 or report['author_cache_reads'] != 0 or report['new_kernel_verification'] is not False:
        raise ValueError('Invalid source-review scope')
    print({'status': 'READ_ONLY_FIXED_GIT_AND_LOG_RECHECK_PASS_NOT_KERNEL',
           'fixed_git_blobs': blob_count, 'actual_log_snapshots': 6,
           'original_D_logs_reopened': not args.snapshots_only,
           'fifths': [26, 11, 165], 'query': [58, 40],
           'lean_started': False, 'kernel_started': False, 'author_cache_used': False})


if __name__ == '__main__':
    main()
