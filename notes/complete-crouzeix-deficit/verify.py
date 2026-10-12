#!/usr/bin/env python3
"""Replay exact checks, validate package integrity, optionally rebuild the PDF."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_check(here, name):
    path = here / name
    if not path.exists():
        return None
    manifest = json.loads(path.read_text())
    for item in manifest['files']:
        target = here / item['path']
        require(target.is_file(), 'Missing manifest file: '+item['path'])
        require(target.stat().st_size == item['bytes'], 'Size mismatch: '+item['path'])
        require(sha(target) == item['sha256'], 'SHA-256 mismatch: '+item['path'])
    return len(manifest['files'])


def run(command, directory):
    result = subprocess.run(command, cwd=directory, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    require(result.returncode == 0, 'Command failed: '+str(command)+'\n'+result.stdout)
    return result.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--build', action='store_true')
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    results = {}
    for checker, expected in [
        ('check_exact.py', 'original_replay.json'),
        ('independent_complex_exact.py', 'independent_replay.json'),
        ('check_disk_comparison.py', 'disk_comparison_replay.json')
    ]:
        normal = run([sys.executable, checker], here/'checks')
        optimized = run([sys.executable, '-O', checker], here/'checks')
        require(normal == optimized, 'Optimization changed result: '+checker)
        require(normal == (here/'checks'/expected).read_text(), 'Stored replay mismatch: '+checker)
        result = json.loads(normal)
        require(result['status'] == 'PASS', 'Checker did not pass: '+checker)
        results[checker] = result
    source_files = manifest_check(here, 'SOURCE_MANIFEST.json')
    release_files = manifest_check(here, 'MANIFEST.json')
    report = {'status':'PASS', 'normal_optimized_identical':True,
              'source_manifest_files_verified':source_files,
              'release_manifest_files_verified':release_files,
              'checks':results,
              'scope':'Exact finite algebra/examples and byte integrity; the written proof supplies analytic and universal statements.'}
    if args.build:
        output = args.output_dir or Path(tempfile.mkdtemp(prefix='crouzeix-rebuild-'))
        output = output.resolve()
        output.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(here/'research.tex', output/'research.tex')
        for iteration in range(1, 4):
            log = run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                       '-halt-on-error', 'research.tex'], output)
            (output/('latex-'+str(iteration)+'.log')).write_text(log)
        require('Overfull' not in log, 'Overfull box in rebuilt PDF')
        require('undefined references' not in log and 'undefined on input' not in log,
                'Unresolved reference in rebuilt PDF')
        info = run(['pdfinfo', 'research.pdf'], output)
        pages = next(int(line.split(':',1)[1]) for line in info.splitlines() if line.startswith('Pages:'))
        require(pages == 12, 'Unexpected PDF page count: '+str(pages))
        run(['pdftotext', '-layout', 'research.pdf', 'paper.txt'], output)
        shutil.copyfile(output/'research.pdf', output/'rebuilt-paper.pdf')
        report['pdf_rebuild'] = {'status':'PASS','pages':pages,
                                 'shell_escape':False,'output_directory':str(output)}
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
