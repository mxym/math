#!/usr/bin/env python3
"""Verify the immutable public package and optionally make a deterministic archive."""
import argparse
import difflib
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[1]
ANCHORS = {
    'cubic_f6_certificate.json': '17858bc398fa8c2c28eb7e6f8398385f98fff53a581dcd59ad42f7f89c3f319c',
    'cubic_rank_one_f8_certificate.json': 'f52f7963c96214244dc15f29616abdc96bdc54ecfd040b3f5f945d57c10fc645',
    'original-verifiers/check_cubic_certificate.py': '29db789dcd5219495baf0c044b339fc789780ed763c161f038e20b0930ad1a7d',
    'original-verifiers/check_rank_one_f8_certificate.py': '810226ffaa92e1c38485d5b8ba17004356933f5a86bcb805d1939f6bbfeca2e5',
    'original-verifiers/independent_check.py': 'b2cf470fbd52073b310b4040a7b42971136caed13eec8f0e6d7ee63c8ae3f3c8',
    'verification/independent_results.json': 'dcbca56d70463c574035fc1fe9aaa015f6369eded9150afb91846f02d04b18be',
}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def safe_name(name):
    return type(name) is str and name and not name.startswith('/') and '..' not in Path(name).parts and str(Path(name)) == name


def integrity():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_bytes())
    whitelist = manifest['whitelist']
    need(type(whitelist) is list and all(safe_name(x) for x in whitelist), 'invalid whitelist')
    need(whitelist == sorted(set(whitelist)), 'whitelist is not sorted/unique')
    actual = []
    for path in ROOT.rglob('*'):
        need(not path.is_symlink(), 'symlink is outside the public file contract')
        if path.is_file():
            actual.append(path.relative_to(ROOT).as_posix())
    need(sorted(actual) == whitelist, 'missing or unexpected package files')
    expected_payload = set(whitelist) - {'MANIFEST.json', 'SHA256SUMS'}
    records = manifest['files']
    need(type(records) is list, 'invalid payload hash list')
    need(len(records) == len(expected_payload) and {x['path'] for x in records} == expected_payload,
         'manifest payload hash inventory mismatch')
    for record in records:
        raw = (ROOT / record['path']).read_bytes()
        need(type(record['bytes']) is int and len(raw) == record['bytes'], 'size mismatch: ' + record['path'])
        need(sha(raw) == record['sha256'], 'hash mismatch: ' + record['path'])
    sums = {}
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        need(name not in sums and safe_name(name), 'invalid SHA256SUMS entry')
        sums[name] = digest
    need(set(sums) == set(whitelist) - {'SHA256SUMS'}, 'SHA256SUMS inventory mismatch')
    for name, digest in sums.items():
        need(sha((ROOT / name).read_bytes()) == digest, 'SHA256SUMS mismatch: ' + name)
    for name, digest in ANCHORS.items():
        need(sha((ROOT / name).read_bytes()) == digest, 'frozen provenance mismatch: ' + name)
    for name in ['check_cubic_certificate.py', 'check_rank_one_f8_certificate.py', 'independent_check.py']:
        old = (ROOT / 'original-verifiers' / name).read_text().splitlines(keepends=True)
        new = (ROOT / name).read_text().splitlines(keepends=True)
        exact = ''.join(difflib.unified_diff(old, new, fromfile='original-verifiers/' + name, tofile=name))
        need(exact == (ROOT / 'verification' / (name + '.patch')).read_text(), 'derivative diff mismatch: ' + name)
    return whitelist


def mathematical_checks():
    checks = [
        ('check_cubic_certificate.py', 'verification/author_f6_results.json'),
        ('check_rank_one_f8_certificate.py', 'verification/author_f8_results.json'),
        ('independent_check.py', 'verification/independent_results.json'),
        ('tools/check_metadata_controls.py', 'verification/metadata_regression_results.json'),
    ]
    for script, fixture in checks:
        expected = (ROOT / fixture).read_bytes()
        for optimized in [False, True]:
            command = [sys.executable, '-B'] + (['-O'] if optimized else []) + [str(ROOT / script)]
            result = subprocess.run(command, cwd=ROOT, capture_output=True,
                env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
            need(result.returncode == 0, 'checker failed: ' + script + '\n' + result.stderr.decode())
            need(result.stdout == expected, 'saved/optimized result mismatch: ' + script)
    return len(checks) * 2


def archive(whitelist, destination):
    destination = destination.resolve()
    need(destination != ROOT and ROOT not in destination.parents,
         'archive destination must be outside the immutable package')
    prefix = 'higher-degree-rank-one-sieves/'
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, compresslevel=9, mtime=0) as compressed:
            with tarfile.open(mode='w', fileobj=compressed, format=tarfile.USTAR_FORMAT) as bundle:
                for name in whitelist:
                    content = (ROOT / name).read_bytes()
                    info = tarfile.TarInfo(prefix + name)
                    info.size = len(content)
                    info.mtime = 0
                    info.uid = info.gid = 0
                    info.uname = info.gname = ''
                    info.mode = 0o644
                    bundle.addfile(info, io.BytesIO(content))
    return sha(destination.read_bytes())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, help='write a deterministic tar.gz outside the package')
    args = parser.parse_args()
    whitelist = integrity()
    reruns = mathematical_checks()
    result = {'status': 'PASS', 'whitelisted_files': len(whitelist),
              'normal_and_optimized_checker_runs': reruns,
              'unchanged_frozen_certificates': 2,
              'exact_derivative_diffs_checked': 3,
              'author_negative_controls_per_certificate': 17,
              'independent_negative_controls_per_certificate': 15,
              'metadata_regressions_per_certificate': 3}
    if args.archive:
        result['archive_sha256'] = archive(whitelist, args.archive)
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
