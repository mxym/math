#!/usr/bin/env python3
"""Verify published bytes and replay exact controls in normal/optimized modes.

Does not turn written analytic claims into kernel-certified statements.
Fresh partial Lean replay is separately documented in README.md.
"""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    manifest = json.loads((HERE / 'MANIFEST.json').read_text())
    files = manifest['files']
    actual = {str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file()
              and p.name != 'MANIFEST.json'
              and not {'.lake', '__pycache__', '.git'}.intersection(p.relative_to(HERE).parts)}
    need(actual == set(files), 'Package inventory differs from sealed manifest')
    for name, record in files.items():
        data = (HERE / name).read_bytes()
        need(len(data) == record['bytes'] and sha256(data).hexdigest() == record['sha256'],
             'Published bytes changed: ' + name)
    for pin in json.loads((HERE / 'SOURCES.json').read_text())['local_files']:
        need(sha256((ROOT / pin['path']).read_bytes()).hexdigest() == pin['sha256'],
             'Changed referenced source: ' + pin['path'])
    outputs = []
    for options in ([], ['-O']):
        result = subprocess.run([sys.executable, '-B', *options, str(HERE / 'checks/exact.py')],
                                capture_output=True)
        need(result.returncode == 0, result.stderr.decode(errors='replace'))
        outputs.append(result.stdout)
    need(outputs[0] == outputs[1] == (HERE / 'results/exact.json').read_bytes(),
         'Normal/optimized/published exact outputs differ')
    lean = json.loads((HERE / 'results/lean.json').read_text())
    need(lean['status'] == 'PASS' and lean['positive_theorems'] == 4 and
         lean['negative_controls_rejected'] == 1, 'Partial Lean report incomplete')
    need(lean['analytic_endpoint_formalized'] is False, 'Wrong formalization scope')
    for name, digest in lean['sources'].items():
        need(sha256((HERE / 'formal' / name).read_bytes()).hexdigest() == digest,
             'Lean source differs from replay: ' + name)
    for name, digest in lean['logs'].items():
        need(sha256((HERE / 'results' / name).read_bytes()).hexdigest() == digest,
             'Lean raw log differs: ' + name)
    pdf = json.loads((HERE / 'results/pdf.json').read_text())
    need(pdf['status'] == 'PASS' and pdf['overfull_hboxes'] == [] and
         pdf['shell_escape'] is False, 'PDF report incomplete')
    for file, key in (('paper.md', 'markdown_sha256'), ('paper.tex', 'tex_sha256'),
                      ('paper.pdf', 'pdf_sha256')):
        need(sha256((HERE / file).read_bytes()).hexdigest() == pdf[key], 'PDF source pin: ' + file)
    print(json.dumps({'status': 'PASS', 'bound_files': len(files),
        'normal_optimized_exact_equal': True,
        'partial_lean_roots': 4, 'empty_kernel_declarations': lean['empty_kernel_declarations'],
        'pdf_pages': pdf['pages'],
        'scope': 'published integrity, exact controls and archived partial-Lean replay'}, indent=2))


if __name__ == '__main__':
    main()
