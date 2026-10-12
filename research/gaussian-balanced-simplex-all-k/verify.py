#!/usr/bin/env python3
"""Package integrity/provenance checker; not a checker for Gaussian analysis."""
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE/'MANIFEST.json').read_text())
    expected = manifest['files']
    actual = {p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file()
              and p.name not in {'MANIFEST.json', 'SHA256SUMS'}
              and '__pycache__' not in p.parts and '.lake' not in p.parts}
    need(actual == set(expected), 'Bound file set changed')
    for name, hash_ in expected.items():
        path = HERE/name
        need(not path.is_symlink() and digest(path) == hash_, 'Hash mismatch: '+name)
    sums = ''.join(hash_+'  '+name+'\n' for name, hash_ in sorted(expected.items()))
    need((HERE/'SHA256SUMS').read_text() == sums, 'Checksum list changed')
    normal = subprocess.run([sys.executable, str(HERE/'check_exact.py')],
                            capture_output=True, check=True).stdout
    optimized = subprocess.run([sys.executable, '-O', str(HERE/'check_exact.py')],
                               capture_output=True, check=True).stdout
    need(normal == optimized == (HERE/'results/exact.json').read_bytes(),
         'Rational diagnostics not replayed identically')
    exact = json.loads(normal)
    need(exact['status'] == 'PASS' and exact['analytic_endpoint_checked'] is False,
         'Diagnostic scope changed')
    lean = json.loads((HERE/'results/lean.json').read_text())
    need(lean['status'] == 'PASS' and lean['positive_theorems'] == 8
         and lean['empty_kernel_declarations'] == 18013
         and lean['negative_controls_rejected'] == 1
         and lean['analytic_endpoint_formalized'] is False, 'Partial Lean scope changed')
    need(set(lean['allowed_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'},
         'Lean axioms changed')
    for name, hash_ in lean['sources'].items():
        need(digest(HERE/'formal'/name) == hash_, 'Lean source changed: '+name)
    for name, hash_ in lean['logs'].items():
        need(digest(HERE/'results'/name) == hash_, 'Lean log changed: '+name)
    for name, namespace in [('Algebra', 'GaussianSimplexAlgebra'),
                            ('RadialComparison', 'GaussianRadialComparison')]:
        text = (HERE/'results'/f'{name}.log').read_text()
        exports = re.findall(r"'("+namespace+r"\.[^']+)' depends on axioms: \[([^]]*)\]", text)
        need(len(exports) == 4, 'Axiom export count: '+name)
        for _, axioms in exports:
            need(set(filter(None, (a.strip() for a in axioms.split(','))))
                 <= set(lean['allowed_axioms']), 'Unexpected exported axiom')
        need('sorry' not in text, 'Admitted positive proof')
    need('EMPTY_KERNEL_REPLAY_PASS 18013 declarations; 8 roots; trust level zero'
         in (HERE/'results/Replay.log').read_text(), 'Replay marker missing')
    false = (HERE/'results/FalseBound.log').read_text()
    need('assumption' in false and 'HasDerivAt h 0 0' in false,
         'Expected omitted-initial-derivative failure missing')
    hpaper = digest(HERE/'paper.md')
    need(manifest['paper_source_sha256'] == hpaper, 'Current manuscript identity changed')
    prior = manifest['prior_paper_source_sha256']
    need(prior == '8416f741398ceb4207edcc3ff31964883ae14044698043bf17a75d66c1dec832',
         'Original manuscript identity changed')
    for name in ['ANALYSIS_FINAL.md', 'COMBINATORICS_FINAL.md']:
        need(prior in (HERE/'review'/name).read_text(), 'Archived review hash missing: '+name)
    review = json.loads((HERE/'review/REVIEW_PROVENANCE.json').read_text())
    revision = json.loads((HERE/'review/REVISION_PROVENANCE.json').read_text())
    need(review['sources']['manuscript_md_sha256'] == prior,
         'Baseline derivation review scope changed')
    need(review['report_sha256'] == digest(HERE/'review/INDEPENDENT_MATHEMATICAL_REVIEW.md')
         == revision['mathematical_review_report_sha256'], 'Current report identity changed')
    need(revision['original_paper_source_sha256'] == prior
         and revision['revised_paper_source_sha256'] == hpaper
         and revision['revised_paper_pdf_sha256'] == digest(HERE/'paper.pdf')
         and revision['revised_paper_tex_sha256'] == digest(HERE/'paper.tex'),
         'Revision identity changed')
    need(revision['whole_136_module_empty_kernel_audit_performed'] is False,
         'Separate Lean audit scope changed')
    info = subprocess.run(['pdfinfo', str(HERE/'paper.pdf')],
                          capture_output=True, check=True).stdout.decode()
    match = re.search(r'^Pages:\s+(\d+)$', info, re.M)
    need(match and int(match[1]) == manifest['pdf_pages'] == revision['revised_pdf_pages'], 'Unexpected PDF page count')
    extracted = subprocess.run(['pdftotext', '-layout', str(HERE/'paper.pdf'), '-'],
                               capture_output=True, check=True).stdout
    need(extracted == (HERE/'results/paper.txt').read_bytes(), 'PDF extracted text differs')
    print(json.dumps({'status': 'PASS', 'bound_files': len(expected), 'pdf_pages': manifest['pdf_pages'],
                      'normal_optimized_exact_equal': True,
                      'partial_lean_roots': 8, 'empty_kernel_declarations': 18013,
                      'scope': 'package integrity, finite rational diagnostics and recorded partial Lean provenance',
                      'analytic_endpoint_machine_checked': False}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
