#!/usr/bin/env python3
"""Compile all self-contained paper sources in fresh temporary directories.

This checks typesetting, not mathematical validity or Lean proofs. It writes
new PDF/source-zip outputs only after all three LaTeX passes succeed and the
final log has no unresolved citations/references, missing glyphs or overfull
boxes. Use each formal package's own reproducer for kernel verification.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent


def build(spec):
    source = HERE / spec['slug']
    # Files explicitly required by the typeset paper or its exact certificate.
    inputs = sorted([p for p in source.iterdir() if p.is_file()
                     and p.suffix in {'.tex', '.py', '.json'}
                     and p.name != 'PROVENANCE.json'])
    with tempfile.TemporaryDirectory(prefix='mxym-preprint-') as temp:
        work = Path(temp)
        for p in inputs:
            shutil.copy2(p, work / p.name)
        for _ in range(3):
            run = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                  '-halt-on-error', 'paper.tex'], cwd=work,
                                 text=True, capture_output=True)
            if run.returncode:
                raise RuntimeError(spec['slug'] + '\n' + run.stdout[-2500:])
        log = (work / 'paper.log').read_text(errors='replace')
        errors = [line for line in log.splitlines() if
                  any(marker in line for marker in
                      ['Overfull', 'undefined', 'Missing character', 'LaTeX Warning'])]
        if errors:
            raise RuntimeError(spec['slug'] + ': ' + repr(errors))
        fonts = subprocess.run(['pdffonts', 'paper.pdf'], cwd=work,
                               check=True, text=True, capture_output=True).stdout
        if re.search(r'\bno\s+(?:yes|no)\s+(?:yes|no)\s+\d+\s+\d+\s*$', fonts, re.M):
            raise RuntimeError('Unembedded font: ' + spec['slug'])
        pdf = (work / 'paper.pdf').read_bytes()
        info = subprocess.run(['pdfinfo', 'paper.pdf'], cwd=work,
                              check=True, text=True, capture_output=True).stdout
        pages = int(re.search(r'^Pages:\s+(\d+)', info, re.M)[1])
        (source / 'paper.pdf').write_bytes(pdf)
        (HERE / 'audit' / (spec['slug'] + '-pdffonts.txt')).write_text(fonts)
        (HERE / 'audit' / (spec['slug'] + '-build.log')).write_text(log)
    # Small self-contained LaTeX upload. Full proof sources are in the DOI archive.
    archive = source / 'paper-source.zip'
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for p in inputs:
            entry = zipfile.ZipInfo(p.name, (2026, 10, 8, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.external_attr = 0o644 << 16
            zf.writestr(entry, p.read_bytes())
    return {'paper': spec['slug'], 'status': 'PASS', 'pages': pages,
            'fresh_temp_compilation': True, 'latex_warnings': [],
            'all_fonts_embedded': True, 'pdf_sha256': hashlib.sha256(pdf).hexdigest(),
            'source_zip_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
            'scope': 'Three fresh LaTeX passes, final log and font embedding; not mathematical or Lean verification.'}


def main():
    (HERE / 'audit').mkdir(exist_ok=True)
    papers = json.loads((HERE / 'CATALOG.json').read_text())['papers']
    results = []
    for spec in papers:
        result = build(spec)
        results.append(result)
        print('TYPESET_PASS', result['paper'], result['pages'], 'pages', flush=True)
    (HERE / 'audit' / 'BUILD_AUDIT.json').write_text(
        json.dumps({'status': 'PASS', 'papers': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
