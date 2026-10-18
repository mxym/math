#!/usr/bin/env python3
"""Read-only source/log binding for C4663, Ecc94 and concrete908199a.
Run with python3 -B. No Lean, Lake, compiler, Git mutation or output writes.
"""
from pathlib import Path
import hashlib
import json
import re
import runpy

HERE = Path(__file__).resolve().parent
PREVIOUS = Path('/mnt/d/math/tmp/extraction-resume-20261018/native-input-binary-generation-independent-review-20261019')
HELPER_SHA = 'e9973afbbb4fcefc38f879557975023cf205aa3abe46340b75ccbd58ea4cd2ae'
PREVIOUS_HASHES = {
    'REPORT.md': '4edc57bde58a57aad45d39756326d606dcfca55b3f5802b122f38dfbc497e76a',
    'MANIFEST.json': '9db209b00d59e523429a673f4751f2745952e968b5c73d9e1e9c038372c95ad7',
    'recheck.py': HELPER_SHA,
}

def digest(data):
    return hashlib.sha256(data).hexdigest()

assert digest((PREVIOUS / 'recheck.py').read_bytes()) == HELPER_SHA
HELPERS = runpy.run_path(str(PREVIOUS / 'recheck.py'))
git, blob, sha, record, closure, evidence = [HELPERS[n] for n in ['git', 'blob', 'sha', 'record', 'closure', 'evidence']]
C = '4663f467c0dc117ef3c9b73403e01006a28fb657'
E = 'cc94df713f82a301400d1d1ef67606d0eec090c3'
M = '908199a025a8dd9f295d3dfa5e4fd3ee1a198986'
CP = 'formalizations/extraction-numerical-synthesis'
EP = 'formalizations/extraction-effective-encoding'
MP = 'formalizations/extraction-concrete-native'

def concrete_evidence():
    path = MP + '/verification/concrete-native-standard-20261019/REPORT.json'
    report = json.loads(blob(M, path))
    sources = []
    for source, expected in report['source_snapshot'].items():
        rec = record(M, source)
        assert rec['sha256'] == expected, ('concrete_source', source)
        sources.append(rec)
    logs, texts = [], {}
    for name, expected in report['logs'].items():
        full = Path('/mnt/d/math/tmp/extraction-resume-20261018/build-logs') / name
        data = full.read_bytes()
        assert sha(data) == expected, ('concrete_log', name)
        logs.append({'path': str(full), 'bytes': len(data), 'sha256': sha(data)})
        texts[name] = data.decode()
    check = texts['20261018T225012777416Z-root-owned-ConcreteNativeExtraction.Check.log']
    aggregate = texts['20261018T225025377675Z-extraction-concrete-native.log']
    for text in [check, aggregate]:
        assert 'CONCRETE_NATIVE_ENDPOINT_DECLARATION_KINDS_CHECK_PASS' in text
    assert 'Build completed successfully (4089 jobs).' in aggregate
    for name, expected in report['axioms'].items():
        assert set(expected) <= {'propext', 'Classical.choice', 'Quot.sound'}
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", check, re.S)
        if expected:
            assert match, ('concrete_axiom_missing', name)
            actual = re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', match.group(1))
            assert sorted(actual) == sorted(expected), ('concrete_axiom_drift', name)
        else:
            assert ("'" + name + "' does not depend on any axioms") in check
    roots = blob(M, MP + '/ROOTS.txt').decode().splitlines()
    models = blob(M, MP + '/MODELS.txt').decode().splitlines()
    assert len(roots) == 8 and len(models) == 3 and models == report['model_roots']
    assert set(roots + models) == set(report['axioms'])
    changed = git('diff', '--name-only', report['parent_head'], M).decode().splitlines()
    assert len(changed) == 12 and all(p.startswith(MP + '/') for p in changed)
    return {'report': record(M, path), 'source_snapshot_entries': sources,
            'original_author_logs': logs, 'successful_standard_jobs': 4089,
            'theorems': roots, 'models': models,
            'actual_log_types_kinds_axioms_checked': True,
            'changes_since_parent_confined_to_new_concrete_package': True}

def gather():
    for name, expected in PREVIOUS_HASHES.items():
        assert sha((PREVIOUS / name).read_bytes()) == expected, ('previous_review_drift', name)
    prior = json.loads((PREVIOUS / 'MANIFEST.json').read_text())
    old_library = Path('/mnt/d/math/tmp/extraction-resume-20261018/native-library-independent-review-20261019')
    for name, expected in prior['prior_review_files_unchanged'].items():
        assert sha((old_library / name).read_bytes()) == expected, ('initial_review_drift', name)
    # The prior mathematical components being extended are unchanged.
    for item in prior['selected_direct_C_sources']:
        assert sha(blob(C, item['path'])) == item['sha256'], ('C_baseline_source_drift', item['path'])
    old_e = {row['path']: row for row in prior['selected_direct_E_sources']}
    for name in ['BinaryNativeExtraction.lean', 'BinaryDescriptorGeneration.lean',
                 'BinaryRankGenerationRecords.lean', 'BinaryRankBranchPrograms.lean',
                 'BinaryRankAlignmentPrograms.lean', 'FullyRetainedNativeExtraction.lean',
                 'RetainedNativeProvider.lean']:
        path = EP + '/EffectiveEncoding/' + name
        assert sha(blob(E, path)) == old_e[path]['sha256'], ('E_baseline_source_drift', path)
        assert sha(blob(M, path)) == old_e[path]['sha256'], ('concrete_baseline_source_drift', path)
    c_names = ['InputNumericalBudgets.lean', 'InputNumericalPower.lean', 'InputNumericalSynthesis.lean', 'InputNumericCheck.lean']
    e_names = ['RetainedInputTarget.lean', 'InputLabelCompilation.lean', 'FullyInputNativeExtraction.lean',
               'InputNativeCheck.lean', 'InputNativeEvaluation.lean']
    for name in c_names[:3]:
        path = CP + '/CircuitNumerical/' + name
        assert blob(E, path) == blob(C, path), ('E_C4663_dependency_drift', path)
    c_evidence = evidence(C, CP + '/verification/input-numeric-aggregate-20261019/REPORT.json', 3974, CP)
    e_evidence = evidence(E, EP + '/verification/input-native-root-check-20261018T224944982159Z/REPORT.json', 4074)
    concrete = concrete_evidence()
    inventory_path = EP + '/INPUT_NATIVE_SOURCE_INVENTORY.json'
    inventory = json.loads(blob(E, inventory_path))
    assert inventory['theorem_count'] == 13 and inventory['model_count'] == 15
    for source in inventory['mathematical_sources']:
        assert sha(blob(E, source['path'])) == source['sha256']
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', HELPERS['strip_comments'](blob(E, source['path']).decode()))
    c_closure = closure(C, CP, ['CircuitNumerical.InputNumericCheck'])
    e_closure = closure(E, EP, ['EffectiveEncoding.InputNativeCheck'])
    m_closure = closure(M, MP, ['ConcreteNativeExtraction.Check'])
    assert 'CircuitNumerical.InputNumericalSynthesis' in e_closure['local_modules']
    assert 'EffectiveEncoding.FullyInputNativeExtraction' in e_closure['local_modules']
    assert 'EffectiveEncoding.FullyInputNativeExtraction' not in m_closure['local_modules']
    assert 'CircuitNumerical.InputNumericalSynthesis' not in m_closure['local_modules']
    for name in ['EffectiveEncoding.NativeBooleanRankProgram', 'EffectiveEncoding.NativeTripleScan',
                 'EffectiveEncoding.NativeTripleWords']:
        assert name not in e_closure['local_modules'], ('unused_successor_became_reachable', name)
    metadata = [record(C, CP + '/' + name) for name in ['INPUT_NUMERIC_ROOTS.txt', 'INPUT_NUMERIC_MODELS.txt', 'INPUT_NUMERIC_SCOPE_20261019.md']]
    metadata += [record(E, EP + '/' + name) for name in ['INPUT_NATIVE_ROOTS.txt', 'INPUT_NATIVE_MODELS.txt',
                   'INPUT_NATIVE_BUILD_ONLY.txt', 'INPUT_NATIVE_SOURCE_INVENTORY.json', 'reproduce_input_native.py']]
    initial = json.loads((old_library / 'MANIFEST.json').read_text())
    initial_binary = json.loads((old_library / 'BINARY_MANIFEST.json').read_text())
    inherited_hashes = [row for row in initial['source_entries']
                        if row['path'].endswith('/RationalGateInterface/Library.lean') or
                        row['path'].endswith('/RationalGateUniversality/Density.lean')]
    inherited_hashes += [row for row in initial_binary['package_entries'] if row['path'].endswith('/RationalGateBinary/Provider.lean')]
    for row in inherited_hashes:
        assert sha(blob(M, row['path'])) == row['sha256'], ('concrete_library_source_drift', row['path'])
    return {
        'status': 'FIXED_C4663_ECC94_CONCRETE908199A_SOURCE_LOG_AND_IMPORT_BINDINGS_READ_ONLY_PASS',
        'fixed_commits': {'C': C, 'E': E, 'concrete': M},
        'previous_review_hashes_unchanged': PREVIOUS_HASHES,
        'initial_library_review_hashes_unchanged': prior['prior_review_files_unchanged'],
        'read_only_helper_sha256': HELPER_SHA,
        'selected_direct_C_sources': [record(C, CP + '/CircuitNumerical/' + n) for n in c_names] + [record(C, CP + '/CircuitNumerical/NativeBudgetAlgebra.lean')],
        'selected_direct_E_sources': [record(E, EP + '/EffectiveEncoding/' + n) for n in e_names],
        'selected_concrete_package_files': [record(M, p) for p in git('ls-tree', '-r', '--name-only', M, MP).decode().splitlines()],
        'selected_scope_metadata': metadata,
        'author_evidence': {'C': c_evidence, 'E': e_evidence, 'concrete': concrete},
        'C_import_binding': c_closure, 'E_import_binding': e_closure, 'concrete_import_binding': m_closure,
        'C_actual_input_numeric338_and_read_same_execution': True,
        'E_full_cached_record_equal_inputCachedRun': True,
        'concrete908199a_integrates_C_read_execution': False,
        'concrete_fixed_net_exists_before_all_k_p_z': True,
        'concrete_library_height_r_plus_one_to_outer_degree9_internal': True,
        'whole_compiler_provider_machine_bit_time_proved': False,
        'new_independent_fresh_kernel_replay_or_strict_controls': False,
        'additional_Lean_or_Lake_or_kernel_execution': False,
        'report_sha256': sha((HERE / 'REPORT.md').read_bytes()),
        'audit_recommendation_sha256': sha((HERE / 'AUDIT_RECOMMENDATION.md').read_bytes()),
        'read_only_script_sha256': sha(Path(__file__).read_bytes()),
    }

if __name__ == '__main__':
    expected = json.loads((HERE / 'MANIFEST.json').read_text())
    actual = gather()
    assert actual == expected, 'Manifest mismatch'
    print(json.dumps({'status': actual['status'], 'manifest_sha256': sha((HERE / 'MANIFEST.json').read_bytes()),
                      'C_modules': len(actual['C_import_binding']['local_modules']),
                      'E_modules': len(actual['E_import_binding']['local_modules']),
                      'concrete_modules': len(actual['concrete_import_binding']['local_modules']),
                      'C_configs': len(actual['C_import_binding']['package_configurations']),
                      'E_configs': len(actual['E_import_binding']['package_configurations']),
                      'concrete_configs': len(actual['concrete_import_binding']['package_configurations']),
                      'additional_Lean_or_Lake_or_kernel_execution': False}, indent=2))
