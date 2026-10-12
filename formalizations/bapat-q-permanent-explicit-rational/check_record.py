#!/usr/bin/env python3
"""Check frozen evidence correspondence; this is not a new Lean execution."""
from hashlib import sha256
import json
from pathlib import Path
import re

from replay import ALLOWED, COMMIT, COMPILER_SHA256, assemble

HERE = Path(__file__).resolve().parent


def need(value, message):
    if not value:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    record = HERE / 'verification'
    report = json.loads((record / 'report.json').read_text())
    need(report['status'] == 'PASS', 'Recorded proof did not pass')
    bundle, roots, sources = assemble(HERE)
    need(bundle.encode() == (record / 'ExplicitBundle.lean').read_bytes(), 'Bundle/source mismatch')
    sources['FalseCoordinateBound.lean'] = digest(HERE / 'FalseCoordinateBound.lean')
    need(sources == report['owned_source_sha256'], 'Owned source hash coverage mismatch')
    need(roots == report['roots'] and len(roots) == report['positive_theorems'] == 30,
         'Owned theorem inventory mismatch')
    need('BapatExplicit.original_conjecture_false_from_explicit' in roots and
         'BapatExplicit.explicit_rational_counterexample' in roots and
         'BapatExplicit.explicitMatrix_rational_entries' in roots,
         'Actual final theorems are absent')
    expected_audit = 'import ExplicitBundle\n' + '\n'.join('#print axioms ' + r for r in roots) + '\n'
    need(expected_audit.encode() == (record / 'AxiomAudit.lean').read_bytes(), 'Axiom audit excludes roots')
    expected_replay = (HERE / 'ReplayTemplate.lean').read_text().replace(
        'ROOT_LIST', '[' + ',\n    '.join('``' + r for r in roots) + ']')
    need(expected_replay.encode() == (record / 'Replay.lean').read_bytes(), 'Replay root inventory mismatch')
    need((HERE / 'FalseCoordinateBound.lean').read_bytes() == (record / 'FalseCoordinateBound.lean').read_bytes(),
         'Negative control changed')
    for name, field in [('replay.py', 'driver_sha256'), ('ReplayTemplate.lean', 'template_sha256'),
                        ('MODULES.json', 'module_inventory_sha256')]:
        need(digest(HERE / name) == report[field], 'Recorded driver/inventory changed: ' + name)
    for field in ['generated_source_sha256', 'log_sha256']:
        for name, expected in report[field].items():
            need(digest(record / name) == expected, 'Recorded payload changed: ' + name)
    need(set(report['generated_source_sha256']) == {
        'ExplicitBundle.lean', 'AxiomAudit.lean', 'Replay.lean', 'FalseCoordinateBound.lean'},
        'Generated source coverage mismatch')
    need(set(report['log_sha256']) == {
        'ExplicitBundle.log', 'AxiomAudit.log', 'Replay.log', 'FalseCoordinateBound.log'},
        'Execution log coverage mismatch')
    axlog = (record / 'AxiomAudit.log').read_text()
    axioms = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", axlog)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", axlog)
    need({name for name, _ in axioms} | set(empty) == set(roots), 'Axiom log coverage mismatch')
    for name, a in axioms:
        need(set(filter(None, (x.strip() for x in a.split(',')))) <= ALLOWED,
             'Unallowed axiom: ' + name)
    match = re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero',
                      (record / 'Replay.log').read_text())
    need(match is not None and int(match[1]) == report['empty_kernel_declarations'] and
         int(match[2]) == len(roots), 'Recorded replay count mismatch')
    false = (record / 'FalseCoordinateBound.log').read_text().lower()
    need(report['negative_controls_rejected'] == 1 and 'decide' in false and 'false' in false,
         'Material false coordinate bound was not rejected')
    expected_codes = {'ExplicitBundle.lean': 0, 'AxiomAudit.lean': 0, 'Replay.lean': 0}
    actual = {c['source']: c['exit'] for c in report['commands'] if 'source' in c}
    need({n: actual.get(n) for n in expected_codes} == expected_codes and
         actual.get('FalseCoordinateBound.lean', 0) != 0, 'Command status mismatch')
    need(report['compiler_git_commit'] == COMMIT and report['compiler_sha256'] == COMPILER_SHA256,
         'Compiler identity mismatch')
    need((HERE / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1', 'Toolchain pin changed')
    manifest = json.loads((HERE / 'lake-manifest.json').read_text())
    revisions = {p['name']: p['rev'] for p in manifest['packages']}
    need(revisions == report['package_revisions'], 'Dependency pins changed')
    need(set(report['allowed_axioms']) == ALLOWED, 'Axiom policy changed')
    original = HERE.parent / 'bapat-q-permanent-counterexample'
    parameters = HERE.parent / 'bapat-q-permanent-dependencies'
    # Check the public inputs, without importing any of their recorded binaries.
    casefile = original / 'evidence/formalization/verify.json'
    need(digest(casefile) == report['original_case_sha256'], 'Original public case changed')
    case = json.loads(casefile.read_text())
    need({v['path']: v['sha256'] for v in case['modules'].values()} == report['original_source_sha256'],
         'Original 22-source inventory mismatch')
    need(set(case['modules']) == set(case['audit_modules']), 'Original audit module coverage changed')
    replay = report['original_replay_summary']
    need(replay['status'] == 'PASS' and replay['trust_level'] == 0 and replay['empty_base'] is True and
         replay['owned_count'] == 928 and replay['all_owned_closure_count'] == 22371,
         'Original all-owned replay scope mismatch')
    need(digest(parameters / 'verification/report.json') == report['parameter_report_sha256'],
         'Published parameter proof record changed')
    published = json.loads((parameters / 'verification/report.json').read_text())
    need(published['owned_source_sha256'] == report['parameter_source_sha256'] and
         report['parameter_empty_kernel_declarations'] == published['empty_kernel_declarations'] == 21571,
         '52-theorem parameter input changed')
    for name, h in report['parameter_source_sha256'].items():
        need(digest(parameters / name) == h, 'Parameter source changed: ' + name)
    need(len(report['imported_owned_artifact_sha256']) == 23,
         'Expected 22 original-module artifacts and one parameter bundle')
    continuation = report.get('original_continuation_report')
    if continuation is not None:
        need(digest(HERE / 'verify_original_input.py') == continuation['driver_sha256'],
             'Original continuation driver changed')
        for name, h in continuation['payload_sha256'].items():
            need(digest(record / 'original-continuation' / name) == h,
                 'Continuation evidence changed: ' + name)
        need(continuation['original_source_sha256'] == report['original_source_sha256'],
             'Continuation input source mismatch')
    print(json.dumps({'status': 'PASS', 'scope': 'Frozen evidence integrity only; not a new Lean replay',
                      'positive_theorems': len(roots),
                      'empty_kernel_declarations': report['empty_kernel_declarations'],
                      'input_modules': 22, 'negative_controls_rejected': 1}, indent=2))


if __name__ == '__main__':
    main()
