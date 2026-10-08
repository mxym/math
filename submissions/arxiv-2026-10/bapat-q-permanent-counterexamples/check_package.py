#!/usr/bin/env python3
"""Fail-closed integrity/source-correspondence check; not a mathematical prover."""
import csv
import hashlib
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    inventory = json.loads((ROOT / 'MANIFEST.json').read_text())
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob('*')
              if p.is_file() and p.name != 'MANIFEST.json' and '__pycache__' not in p.parts}
    require(actual == set(inventory['sha256']), 'File inventory differs from manifest')
    for name, expected in inventory['sha256'].items():
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected,
                'Checksum mismatch: ' + name)
    build = json.loads((ROOT / 'qa/BUILD_REPORT.json').read_text())
    with zipfile.ZipFile(ROOT / 'bapat-arxiv-source.zip') as z:
        require(set(z.namelist()) == set(build['source_sha256']), 'ZIP inventory mismatch')
        for name, digest in build['source_sha256'].items():
            raw = z.read(name)
            require(raw == (ROOT / name).read_bytes(), 'ZIP/source byte mismatch: ' + name)
            require(hashlib.sha256(raw).hexdigest() == digest, 'ZIP recorded hash mismatch')
    require(hashlib.sha256((ROOT / 'paper.pdf').read_bytes()).hexdigest() == build['pdf_sha256'],
            'PDF/build record mismatch')
    tex = (ROOT / 'main.tex').read_text()
    labels = re.findall(r'\\label\{([^}]+)\}', tex)
    refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)
    cites = [k.strip() for group in re.findall(r'\\cite\{([^}]+)\}', tex) for k in group.split(',')]
    bib = re.findall(r'\\bibitem\{([^}]+)\}', tex)
    require(len(labels) == len(set(labels)), 'Duplicate TeX label')
    require(not (set(refs) - set(labels)), 'Missing TeX reference')
    require(not (set(cites) - set(bib)), 'Missing bibliography item')
    with (ROOT / 'anc/counterexample_vectors_n200.csv').open() as f:
        rows = list(csv.DictReader(f))
    expected = {i + 1: tuple(int(r[k]) for k in ['a_real', 'a_imag', 'b_real', 'b_imag'])
                for i, r in enumerate(rows)}
    table = {}
    for line in (ROOT / 'witness.tex').read_text().splitlines():
        if not re.match(r'^\d+ &', line):
            continue
        for m in re.finditer(r'(\d+) & \$\(([-\d,]+)\)\$', line):
            i = int(m[1])
            require(i not in table, 'Repeated witness index')
            table[i] = tuple(map(int, m[2].split(',')))
    require(len(expected) == 200 and table == expected, 'Witness table/CSV mismatch')
    print('PACKAGE_INTEGRITY_AND_SOURCE_CORRESPONDENCE_PASS')
    print('This does not rerun TeX, exact arithmetic, Lean, or mathematical peer review.')


if __name__ == '__main__':
    main()
