#!/usr/bin/env python3
"""Read-only byte/evidence recheck. Does not invoke Lean, Lake, a compiler, or a build.

Run in Ubuntu-22.04: python3 /mnt/d/math/tmp/extraction-resume-20261018/native-library-independent-review-20261019/recheck.py
Only existing fixed Git objects, Mathlib files, logs and this report are read.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = Path('/home/mxym/math-extraction-lean-minimax-20261016')
MATHLIB = Path('/mnt/lean-research-d/cache/mathlib-d13f23b7-extended')
LOGDIR = Path('/mnt/d/math/tmp/extraction-resume-20261018/build-logs')
U = '68e1175648097b1ba240d9dffb718805aa22d699'
US = '2afbc1694cae6209b4b010212e485ac98a8304ad'
P = 'd3c249ef46886ec80a31afecd8a4b0e0b7269f23'
I = 'fce6bf635f1bc100e26c8544517586c72dc228fc'
UP = 'formalizations/extraction-rational-gate-universality'
PP = 'formalizations/extraction-rational-gate-provider'
IP = 'formalizations/extraction-rational-gate-interface'
PIN = 'd13f23b723b8a846827a245b89c10fc7d3f11612'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args, repo=REPO):
    return subprocess.check_output(['git', '-C', str(repo), *args])

def blob(commit, path):
    return git('show', commit + ':' + path)

def record(commit, path):
    data = blob(commit, path)
    return {'commit': commit, 'path': path,
            'git_blob': git('rev-parse', commit + ':' + path).decode().strip(),
            'bytes': len(data), 'sha256': sha(data)}

def check_snapshot(commit, snapshot, prefix=''):
    for path, expected in snapshot.items():
        full = (prefix + '/' + path) if prefix else path
        assert sha(blob(commit, full)) == expected, ('source_snapshot', commit, full)

def gather():
    reports = {
        'universality': (US, UP + '/verification/author-standard-20261019/REPORT.json'),
        'provider19': (P, PP + '/verification/standard-fifths8f-20261019/REPORT.json'),
        'geometry9': (P, PP + '/verification/geometry-standard-20261019/REPORT.json'),
        'interface6': (I, IP + '/verification/library-standard-20261019/REPORT.json'),
    }
    parsed = {name: json.loads(blob(*where)) for name, where in reports.items()}
    ur, pr, gr, ir = [parsed[x] for x in ['universality', 'provider19', 'geometry9', 'interface6']]
    check_snapshot(U, ur['source_snapshot'])
    check_snapshot(pr['source_commit'], pr['source_snapshot'])
    check_snapshot(P, gr['mathematical_source_snapshot'], PP)
    check_snapshot(I, ir['source_snapshot'])
    inventory = json.loads(blob(U, UP + '/SOURCE_INVENTORY.json'))
    check_snapshot(U, inventory['owned_inputs'], UP)
    owned = json.loads(blob(US, UP + '/verification/author-standard-20261019/OWNED_INPUTS.json'))
    check_snapshot(U, owned)
    seal = json.loads(blob(US, UP + '/verification/author-standard-20261019/SEALED_FILES.json'))
    check_snapshot(US, seal['files'], UP + '/verification/author-standard-20261019')
    closure = json.loads(blob(US, UP + '/verification/author-standard-20261019/IMPORT_CLOSURE.json'))
    assert closure['source_commit'] == U
    for name, entry in closure['local_modules'].items():
        assert sha(blob(U, entry['path'])) == entry['sha256'], ('closure_sha', name)
        assert git('rev-parse', U + ':' + entry['path']).decode().strip() == entry['git_blob'], ('closure_blob', name)
    check_snapshot(U, closure['configuration_inputs'])
    entries = []
    for commit, prefix in [(US, UP), (P, PP), (I, IP)]:
        for path in git('ls-tree', '-r', '--name-only', commit, prefix).decode().splitlines():
            entries.append(record(commit, path))
    reviewed_dependencies = [
        'PrecomputedNet.lean', 'QuaternionPlane.lean', 'SU2Coordinates.lean',
        'QuaternionOracles.lean', 'SpecialUnitaryNet.lean', 'FiniteNet.lean',
    ]
    for name in reviewed_dependencies:
        entries.append(record(I, 'formalizations/extraction-circuit-recursion/CircuitRecursion/' + name))
    closure_entries = [record(U, e['path']) for e in closure['local_modules'].values()]
    closure_configs = [record(U, path) for path in closure['configuration_inputs']]
    logs = {
        '20261018T222420050100Z-extraction-rational-gate-universality.log': ur['original_log_sha256'],
        '20261018T214911355721Z-extraction-rational-gate-provider.log': pr['log_sha256'],
        **gr['logs'], **ir['logs'],
    }
    log_entries = []
    log_text = {}
    for name, expected in logs.items():
        data = (LOGDIR / name).read_bytes()
        assert sha(data) == expected, ('original_log_hash', name)
        log_entries.append({'path': str(LOGDIR / name), 'bytes': len(data), 'sha256': sha(data)})
        log_text[name] = data.decode()
    assert blob(US, UP + '/verification/author-standard-20261019/build.log') == (
        LOGDIR / '20261018T222420050100Z-extraction-rational-gate-universality.log').read_bytes()
    for name, jobs in [
        ('20261018T222420050100Z-extraction-rational-gate-universality.log', 3883),
        ('20261018T214911355721Z-extraction-rational-gate-provider.log', 3097),
        ('20261018T220008401275Z-extraction-rational-gate-provider.log', 3111),
        ('20261018T221517548273Z-extraction-rational-gate-interface.log', 3864),
    ]:
        assert f'Build completed successfully ({jobs} jobs).' in log_text[name], ('build_terminal', name)
    assert 'RATIONAL_GATE_PROVIDER_DATA_CHECK_PASS' in log_text['20261018T221517548273Z-extraction-rational-gate-interface.log']
    # Check the actual log's axiom text, not only the author's parsed JSON.
    for report, axkey, names in [
        (ur, 'axioms', ['20261018T222420050100Z-extraction-rational-gate-universality.log']),
        (pr, 'reported_axioms', ['20261018T214911355721Z-extraction-rational-gate-provider.log']),
        (gr, 'axioms', ['20261018T215955831058Z-root-owned-RationalGateProvider.GeometryCheck.log']),
        (ir, 'axioms', ['20261018T221509196724Z-root-owned-RationalGateInterface.Check.log']),
    ]:
        text = '\n'.join(log_text[n] for n in names)
        for decl, expected in report[axkey].items():
            match = re.search(r"'" + re.escape(decl) + r"' depends on axioms: \[([^]]*)\]", text, re.S)
            if not expected:
                assert ("'" + decl + "' does not depend on any axioms") in text or (match and not match.group(1).strip()), ('axioms_empty', decl)
            else:
                assert match, ('missing_log_axioms', decl)
                actual = re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', match.group(1))
                assert sorted(actual) == sorted(expected), ('axioms_drift', decl, actual)
    assert git('rev-parse', 'HEAD', repo=MATHLIB).decode().strip() == PIN
    mathlib_paths = [
        'Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean',
        'Mathlib/Topology/Instances/AddCircle/DenseSubgroup.lean',
        'Mathlib/Topology/Algebra/Group/Subgroup.lean',
        'Mathlib/Topology/DenseEmbedding.lean',
    ]
    mathlib = []
    for path in mathlib_paths:
        data = (MATHLIB / path).read_bytes()
        assert data == git('show', PIN + ':' + path, repo=MATHLIB), ('mathlib_working_copy', path)
        mathlib.append({'path': str(MATHLIB / path), 'git_blob': git('rev-parse', PIN + ':' + path, repo=MATHLIB).decode().strip(), 'bytes': len(data), 'sha256': sha(data)})
    return {
        'status': 'FIXED_GIT_SOURCES_AUTHOR_LOGS_AND_IMPORT_BINDING_READ_ONLY_PASS',
        'fixed_commits': {'universality_mathematics': U, 'universality_author_seal': US, 'provider_and_geometry': P, 'interface': I},
        'mathlib_pin': PIN, 'source_entries': entries,
        'import_closure_entries': closure_entries, 'import_closure_configs': closure_configs,
        'original_author_logs': log_entries, 'read_mathlib_API_entries': mathlib,
        'selected_author_standard_counts': {'provider19_jobs': 3097, 'geometry9_jobs': 3111, 'interface6_jobs': 3864, 'universality13_theorems_4_definitions_jobs': 3883},
        'checked_snapshots_and_inventories': True,
        'checked_actual_log_axiom_text': True,
        'additional_Lean_or_Lake_or_kernel_execution': False,
        'independent_fresh_kernel_replay': False,
        'new_strict_controls': False,
        'review_report_sha256': sha((HERE / 'REPORT.md').read_bytes()),
        'read_only_recheck_script_sha256': sha(Path(__file__).read_bytes()),
    }

if __name__ == '__main__':
    expected = json.loads((HERE / 'MANIFEST.json').read_text())
    actual = gather()
    assert actual == expected, 'Manifest mismatch'
    print(json.dumps({'status': actual['status'], 'manifest_sha256': sha((HERE / 'MANIFEST.json').read_bytes()),
                      'source_entries': len(actual['source_entries']),
                      'closure_modules': len(actual['import_closure_entries']),
                      'closure_configs': len(actual['import_closure_configs']),
                      'original_author_logs': len(actual['original_author_logs']),
                      'additional_Lean_or_Lake_or_kernel_execution': False}, indent=2))
