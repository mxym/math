#!/usr/bin/env python3
"""Build the Bapat arXiv source package in a fresh directory, shell escape off."""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
PAPER = HERE / 'bapat-q-permanent-counterexamples'
FILES = ['main.tex', 'witness.tex', 'anc/README.md',
         'anc/counterexample_vectors_n200.csv', 'anc/expected_values.json',
         'anc/verify_recurrence.py', 'anc/verify_pairs.py']


def run(args, work, env=None):
    result = subprocess.run(args, cwd=work, env=env, text=True,
                            capture_output=True, timeout=180)
    if result.returncode:
        raise RuntimeError(str(args) + '\n' + (result.stdout + result.stderr)[-5000:])
    return result.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True,
                        help='A new directory outside the source tree')
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    for executable in ['pdflatex', 'pdfinfo', 'pdffonts', 'pdftotext']:
        if not shutil.which(executable):
            raise RuntimeError('Required executable missing: ' + executable)
    archive = output / 'bapat-arxiv-source.zip'
    hashes = {}
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
        for name in FILES:
            raw = (PAPER / name).read_bytes()
            item = zipfile.ZipInfo(name, (2026, 10, 8, 0, 0, 0))
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = 0o644 << 16
            z.writestr(item, raw)
            hashes[name] = hashlib.sha256(raw).hexdigest()
    with tempfile.TemporaryDirectory(prefix='bapat-arxiv-build-') as temp:
        work = Path(temp)
        with zipfile.ZipFile(archive) as z:
            if sorted(z.namelist()) != sorted(FILES):
                raise RuntimeError('Unexpected archive inventory')
            z.extractall(work)
        for name, digest in hashes.items():
            if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
                raise RuntimeError('Extracted source hash mismatch: ' + name)
        env = os.environ.copy()
        env.update(SOURCE_DATE_EPOCH='1791460800', FORCE_SOURCE_DATE='1')
        for i in range(3):
            console = run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                           '-halt-on-error', '-file-line-error', 'main.tex'], work, env)
            (output / ('build-pass%d.txt' % (i + 1))).write_text(console)
        log = (work / 'main.log').read_text()
        prohibited = ['Overfull', 'Underfull', 'undefined references',
                      'undefined on input', 'multiply defined', 'Missing character',
                      'Label(s) may have changed', 'Table widths have changed',
                      'Column widths have changed']
        for token in prohibited:
            if token in log:
                raise RuntimeError('Final TeX diagnostic: ' + token)
        shutil.copyfile(work / 'main.pdf', output / 'paper.pdf')
        shutil.copyfile(work / 'main.log', output / 'build-final.log')
        info = run(['pdfinfo', 'main.pdf'], work)
        fonts = run(['pdffonts', 'main.pdf'], work)
        if 'Type 3' in fonts:
            raise RuntimeError('Bitmap font in PDF')
        for line in fonts.splitlines()[2:]:
            fields = line.split()
            # Final six columns: emb/sub/uni/object/ID; encoding precedes them.
            if fields[-5] != 'yes':
                raise RuntimeError('Unembedded font: ' + line)
        pdftext = run(['pdftotext', '-layout', 'main.pdf', '-'], work)
        for text in ['Yongxian Zhang', '200', '54,739', '22,812',
                     'integer', 'References', '0009-0000-3864-3536']:
            if text not in pdftext:
                raise RuntimeError('Expected PDF text missing: ' + text)
        (output / 'paper.txt').write_text(pdftext)
        (output / 'pdfinfo.txt').write_text(info)
        (output / 'pdffonts.txt').write_text(fonts)
        (output / 'bbox.html').write_text(run(['pdftotext', '-bbox', 'main.pdf', '-'], work))
        exact = []
        for script in ['verify_recurrence.py', 'verify_pairs.py']:
            text = run(['python3', 'anc/' + script], work)
            (output / (script + '.txt')).write_text(text)
            exact.append({'script': script, 'result': 'PASS'})
            rejected = subprocess.run(['python3', '-O', 'anc/' + script], cwd=work,
                                      text=True, capture_output=True)
            if rejected.returncode == 0 or 'Run without -O' not in rejected.stderr:
                raise RuntimeError('Optimized execution guard failed: ' + script)
        # A deliberately false rank-one input must fail both certificate programs.
        with (work / 'anc/counterexample_vectors_n200.csv').open('w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['a_real', 'a_imag', 'b_real', 'b_imag'])
            writer.writerows([(1, 0, 0, 0)] * 200)
        for script in ['verify_recurrence.py', 'verify_pairs.py']:
            rejected = subprocess.run(['python3', 'anc/' + script], cwd=work,
                                      text=True, capture_output=True, timeout=180)
            if rejected.returncode == 0:
                raise RuntimeError('False-certificate control accepted: ' + script)
            (output / (script + '.false-control.txt')).write_text(rejected.stdout + rejected.stderr)
    report = {'status': 'PASS', 'scope': 'Source-archive build, text/layout diagnostics and exact complex certificate; not a new Lean replay or external peer review',
              'source_sha256': hashes, 'source_archive_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
              'pdf_sha256': hashlib.sha256((output / 'paper.pdf').read_bytes()).hexdigest(),
              'pages': int(re.search(r'Pages:\s+(\d+)', info)[1]),
              'tex_passes': 3, 'shell_escape': False, 'exact_checkers': exact,
              'optimized_execution_controls_rejected': 2, 'false_certificate_controls_rejected': 2,
              'pdf_fonts_embedded': True, 'bitmap_fonts': 0,
              'final_tex_diagnostics': {token: 0 for token in prohibited}}
    (output / 'BUILD_REPORT.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'pages': report['pages'],
                      'output': str(output)}, indent=2))


if __name__ == '__main__':
    main()
