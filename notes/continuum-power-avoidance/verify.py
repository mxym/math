#!/usr/bin/env python3
"""Offline exact replay and byte-integrity verification; optional PDF rebuild."""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_manifest(here, name):
    path = here / name
    if not path.exists():
        return None
    data = json.loads(path.read_text())
    for row in data['files']:
        target = here / row['path']
        need(target.is_file(), 'Missing file: ' + row['path'])
        need(target.stat().st_size == row['bytes'], 'Size mismatch: ' + row['path'])
        need(digest(target.read_bytes()) == row['sha256'], 'Hash mismatch: ' + row['path'])
    return data


def command(args, cwd):
    result = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    need(result.returncode == 0,
         'Command failed: ' + ' '.join(map(str, args)) + '\n' + result.stderr.decode(errors='replace') + result.stdout.decode(errors='replace'))
    return result.stdout


def replay(here):
    reports = {}
    for checker, expected in (
        ('check_exact.py', 'submitted_expected.json'),
        ('independent_oracles.py', 'independent_expected.json'),
    ):
        outputs = [command([sys.executable, '-B'] + (['-O'] if mode else []) +
                           [str(here / 'checks' / checker)], here) for mode in (False, True)]
        need(outputs[0] == outputs[1], 'Normal/-O difference: ' + checker)
        need(outputs[0] == (here / 'checks' / expected).read_bytes(), 'Stored exact report mismatch: ' + checker)
        report = json.loads(outputs[0])
        need(report['status'] == 'PASS', 'Finite checker did not pass: ' + checker)
        reports[checker] = {'status': 'PASS', 'normal_optimized_byte_identical': True,
                            'report_sha256': digest(outputs[0])}
    return reports


def check_archive(here, source):
    archive = here / 'source.tar.gz'
    if not archive.exists():
        return None
    expected = source['archive_members']
    with tarfile.open(archive, 'r:gz') as tar:
        members = tar.getmembers()
        names = [m.name for m in members]
        need(names == expected, 'Source archive member list/order mismatch')
        for item in members:
            need(item.isfile() and not item.issym() and not item.islnk(), 'Unsafe archive member')
            need(not item.name.startswith('/') and '..' not in Path(item.name).parts, 'Unsafe archive path')
            need(item.mtime == 0 and item.uid == 0 and item.gid == 0, 'Nondeterministic tar metadata')
            need(tar.extractfile(item).read() == (here / item.name).read_bytes(), 'Archive byte mismatch: ' + item.name)
    return {'status': 'PASS', 'member_count': len(expected), 'sha256': digest(archive.read_bytes())}


def build(here, output):
    output.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(here / 'paper.tex', output / 'paper.tex')
    for iteration in range(1, 4):
        log = command(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                       '-halt-on-error', 'paper.tex'], output)
        (output / ('build-' + str(iteration) + '.txt')).write_bytes(log)
    text = log.decode(errors='replace')
    need('Overfull' not in text, 'Overfull box in rebuilt PDF')
    need('undefined references' not in text and 'undefined on input' not in text,
         'Unresolved reference in rebuilt PDF')
    info = command(['pdfinfo', 'paper.pdf'], output).decode()
    pages = next(int(line.split(':', 1)[1]) for line in info.splitlines() if line.startswith('Pages:'))
    recorded = json.loads((here / 'VERIFICATION.json').read_text())['pdf']['pages']
    need(pages == recorded, 'Unexpected PDF page count')
    command(['pdftotext', '-layout', 'paper.pdf', 'paper.txt'], output)
    text = (output / 'paper.txt').read_text()
    need('One avoiding set for all real powers' in text, 'Missing theorem conclusion in PDF')
    need('A sparse-block obstruction for this mechanism' in text, 'Missing sparse-block proof in PDF')
    return {'status': 'PASS', 'pages': pages, 'shell_escape': False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--build', action='store_true')
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    references = json.loads((here / 'REFERENCE_MANIFEST.json').read_text())
    for name, row in references.items():
        data = (here / 'sources' / name).read_bytes()
        need(len(data) == row['bytes'] and digest(data) == row['sha256'], 'Pinned reference mismatch: ' + name)
    source = read_manifest(here, 'SOURCE_MANIFEST.json')
    need(source is not None, 'SOURCE_MANIFEST.json is required')
    release = read_manifest(here, 'MANIFEST.json')
    whitelist = here / 'PUBLICATION_WHITELIST.json'
    if release and whitelist.exists():
        allowed = json.loads(whitelist.read_text())['files']
        actual = sorted(str(p.relative_to(here)) for p in here.rglob('*') if p.is_file())
        need(actual == allowed, 'Release whitelist mismatch')
    elif not release:
        actual = sorted(str(p.relative_to(here)) for p in here.rglob('*') if p.is_file())
        need(actual == source['archive_members'], 'Clean-source member mismatch')
    report = {'status': 'PASS', 'checks': replay(here),
              'reference_file_count': len(references),
              'mathematical_reference_component_count': 6,
              'source_manifest_hashed_files': len(source['files']),
              'source_archive_member_count': len(source['archive_members']),
              'release_manifest_hashed_files': len(release['files']) if release else None,
              'source_archive': check_archive(here, source),
              'scope': 'Exact finite controls and byte integrity. The written proof establishes the infinite theorem; no Lean, novelty, or practical construction certificate.'}
    if args.build:
        output = (args.output_dir or Path(tempfile.mkdtemp(prefix='continuum-proof-rebuild-'))).resolve()
        report['pdf_rebuild'] = build(here, output)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
