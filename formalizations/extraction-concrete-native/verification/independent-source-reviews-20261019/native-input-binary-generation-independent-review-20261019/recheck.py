#!/usr/bin/env python3
"""Read-only recheck for the fixed C788/E2f2 source review.
Run with python3 -B. Never invokes Lean, Lake, compilation, or a Git write.
"""
from pathlib import Path
import hashlib
import json
import posixpath
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = Path('/home/mxym/math-extraction-lean-minimax-20261016')
C = '7882995102f1d59b863e3b8d510d588600a2eba7'
E = '2f2ff15e6680d102b8aa11cead10bc3396443ca4'
CP = 'formalizations/extraction-numerical-synthesis'
EP = 'formalizations/extraction-effective-encoding'
PIN = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
OLD = Path('/mnt/d/math/tmp/extraction-resume-20261018/native-library-independent-review-20261019')
OLD_HASHES = {
    'REPORT.md': 'c8333fdaff98cd9e08628ca45b57cfe5d34340646134e32f09f2438bd0194b1f',
    'MANIFEST.json': '512260dc06784f384c2799c8659a1dd41258f3724f7b7f582c5d2fab46768016',
    'BINARY_APPENDIX.md': '94fe5ce5d99c612dd621230c42d39f4c38a55b5879a853052edf1214814b9607',
    'BINARY_MANIFEST.json': 'f547cd2e72c73de4b4340fed6324972b65c3ec1709a8158bfb86ddfbe37c4880',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])

def blob(commit, path):
    return git('show', commit + ':' + path)

def record(commit, path):
    data = blob(commit, path)
    return {'commit': commit, 'path': path,
            'git_blob': git('rev-parse', commit + ':' + path).decode().strip(),
            'bytes': len(data), 'sha256': sha(data)}

def strip_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1; out.extend('  '); i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1; out.extend('  '); i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            if j == -1:
                break
            out.append('\n'); i = j + 1
        else:
            out.append(text[i]); i += 1
    assert depth == 0
    return ''.join(out)

def closure(commit, prefix, targets):
    paths = set(git('ls-tree', '-r', '--name-only', commit).decode().splitlines())
    manifest = json.loads(blob(commit, prefix + '/lake-manifest.json'))
    roots = [prefix] + [posixpath.normpath(prefix + '/' + p['dir'])
                        for p in manifest['packages'] if p['type'] == 'path']
    assert len(set(roots)) == len(roots)
    modules = {}
    for root in roots:
        for path in paths:
            if path.startswith(root + '/') and path.endswith('.lean') and '/.lake/' not in path:
                relative = path[len(root)+1:]
                if relative != 'lakefile.lean':
                    modules.setdefault(relative[:-5].replace('/', '.'), []).append(path)
    visited, external, todo = {}, set(), list(targets)
    while todo:
        name = todo.pop()
        if name in visited:
            continue
        candidates = modules.get(name, [])
        assert len(candidates) == 1, ('module_resolution', name, candidates)
        path = candidates[0]
        imports = []
        for line in strip_comments(blob(commit, path).decode()).splitlines():
            match = re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+)$', line)
            if match:
                imports.extend(match.group(1).split())
        visited[name] = {**record(commit, path), 'imports': imports}
        for imported in imports:
            if imported in modules:
                todo.append(imported)
            else:
                assert imported.split('.')[0] in ['Mathlib', 'Lean', 'Std', 'Batteries', 'Qq', 'Aesop'], ('unresolved_external', imported)
                external.add(imported)
    configs = []
    for root in roots:
        for name in ['lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
            path = root + '/' + name
            if path in paths:
                configs.append(record(commit, path))
    return {'entry_modules': targets, 'local_modules': dict(sorted(visited.items())),
            'external_import_names': sorted(external), 'package_configurations': configs}

def evidence(commit, report_path, expected_jobs, source_prefix=''):
    report = json.loads(blob(commit, report_path))
    snapshot = report.get('inputs', report.get('source_sha256'))
    assert isinstance(snapshot, dict)
    sources = []
    for path, expected in snapshot.items():
        full = path if path.startswith('formalizations/') else source_prefix + '/' + path
        rec = record(commit, full)
        assert rec['sha256'] == expected, ('author_source_snapshot', full)
        sources.append(rec)
    path = Path(report.get('log', report.get('check_log')))
    data = path.read_bytes()
    assert sha(data) == report.get('log_sha256', report.get('check_log_sha256'))
    text = data.decode()
    assert f'Build completed successfully ({expected_jobs} jobs).' in text
    axioms = report.get('axioms', report.get('root_axioms'))
    assert isinstance(axioms, dict)
    for name, expected in axioms.items():
        assert set(expected) <= {'propext', 'Classical.choice', 'Quot.sound'}
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", text, re.S)
        if expected:
            assert match, ('missing_log_axioms', name)
            actual = re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', match.group(1))
            assert sorted(actual) == sorted(expected), ('log_axiom_drift', name, actual)
        else:
            assert ("'" + name + "' does not depend on any axioms") in text or (match and not match.group(1).strip()), ('empty_log_axioms', name)
    if 'roots' in report:
        assert len(report['roots']) == report['theorem_count']
        assert len(report['models']) == report['model_count']
        marker = f"OWNED_KIND_CHECK_PASS {report['theorem_count']} theorems; {report['model_count']} models"
        assert marker in text
    return {'report': record(commit, report_path), 'author_report_status': report['status'],
            'reported_checkout_head': report['source_head'],
            'source_snapshot_entries': sources, 'actual_log': {'path': str(path), 'bytes': len(data), 'sha256': sha(data)},
            'successful_standard_jobs': expected_jobs,
            'selected_theorems': report.get('theorem_count', report.get('theorem_roots')),
            'selected_models': report.get('model_count', report.get('model_declarations')),
            'actual_log_axiom_entries': len(axioms)}

def gather():
    for name, expected in OLD_HASHES.items():
        assert sha((OLD / name).read_bytes()) == expected, ('prior_report_changed', name)
    c_deps = ['NativeListLookup.lean', 'NativeLinearPacketCache.lean', 'NativeLinearCachedSynthesis.lean']
    for name in c_deps:
        path = CP + '/CircuitNumerical/' + name
        assert blob(C, path) == blob('c64157509fd2686e68fd090d8b58717f6545b976', path)
    records = {
        'C_input_cache': evidence(C, CP + '/verification/input-cache-aggregate-20261019/REPORT.json', 3967, CP),
        'C_input_word': evidence(C, CP + '/verification/input-word-aggregate-20261019/REPORT.json', 3971, CP),
        'E_retained_provider': evidence(E, EP + '/verification/retained-native-provider-root-check-20261018T222708685222Z/REPORT.json', 4050),
        'E_binary_rank_endpoint': evidence(E, EP + '/verification/binary-rank-endpoint-root-check-20261018T223228900277Z/REPORT.json', 4022),
        'E_binary_generation': evidence(E, EP + '/verification/binary-generation-root-check-20261018T223717066507Z/REPORT.json', 4058),
    }
    inventory = json.loads(blob(E, EP + '/BINARY_GENERATION_SOURCE_INVENTORY.json'))
    assert inventory['theorem_count'] == 29 and inventory['model_count'] == 23
    for source in inventory['mathematical_sources']:
        assert sha(blob(E, source['path'])) == source['sha256']
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', strip_comments(blob(E, source['path']).decode()))
    c_extra = [CP + '/' + f for f in [
        'INPUT_CACHE_ROOTS.txt', 'INPUT_CACHE_MODELS.txt', 'INPUT_CACHE_SCOPE_20261019.md',
        'INPUT_WORD_ROOTS.txt', 'INPUT_WORD_MODELS.txt', 'INPUT_WORD_SCOPE_20261019.md']]
    e_extra = [EP + '/' + f for f in [
        'BINARY_GENERATION_ROOTS.txt', 'BINARY_GENERATION_MODELS.txt', 'BINARY_GENERATION_BUILD_ONLY.txt',
        'BINARY_GENERATION_SOURCE_INVENTORY.json', 'reproduce_binary_generation.py']]
    # Retain fixed identities for selected direct sources in addition to the full import graph.
    c_read = c_deps + [
        'InputCacheExpressions.lean', 'InputCacheEvaluation.lean', 'InputCacheBudgets.lean',
        'InputCacheOracles.lean', 'InputNumericalExecution.lean', 'InputTraceRefinement.lean',
        'InputCachedSynthesis.lean', 'InputCachePolynomial.lean', 'InputWordCheck.lean']
    e_read = [
        'BinaryRankGenerationRecords.lean', 'BinaryRankBranchPrograms.lean', 'BinaryRankAlignmentPrograms.lean',
        'BinaryDescriptorGeneration.lean', 'BinaryNativeExtraction.lean', 'BinaryGenerationCheck.lean',
        'BinaryGenerationEvaluation.lean', 'NativeBinaryRankEndpoints.lean', 'FixedWidthEndpointBits.lean',
        'UnaryWordEncoding.lean', 'CarriedOccupationRank.lean', 'ConstructiveTriples.lean',
        'ConstructiveRankExtraction.lean', 'RankByTriples.lean', 'NativeOccupationSelection.lean',
        'PreparedNativeGeneration.lean', 'RetainedNativeProvider.lean', 'RetainedProviderLabels.lean',
        'FullyRetainedNativeExtraction.lean', 'NativeProviderBooleanBudgets.lean', 'NativeProviderRefinement.lean',
        'ActualNativeNumericalBudget.lean', 'FullyNativeExtraction.lean', 'RetainedNativeProviderEvaluation.lean']
    return {
        'status': 'FIXED_C788_E2F2_SOURCES_STANDARD_LOGS_AND_LOCAL_IMPORT_BINDINGS_READ_ONLY_PASS',
        'fixed_commits': {'C': C, 'E': E}, 'mathlib_pin': PIN,
        'prior_review_files_unchanged': OLD_HASHES,
        'selected_direct_C_sources': [record(C, CP + '/CircuitNumerical/' + n) for n in c_read],
        'selected_direct_E_sources': [record(E, EP + '/EffectiveEncoding/' + n) for n in e_read],
        'selected_scope_metadata': [record(C, p) for p in c_extra] + [record(E, p) for p in e_extra],
        'author_evidence': records,
        'C_import_binding': closure(C, CP, ['CircuitNumerical.InputCacheCheck', 'CircuitNumerical.InputWordCheck']),
        'E_import_binding': closure(E, EP, ['EffectiveEncoding.RetainedNativeProviderCheck', 'EffectiveEncoding.BinaryRankEndpointCheck', 'EffectiveEncoding.BinaryGenerationCheck']),
        'read_report_sha256': sha((HERE / 'REPORT.md').read_bytes()),
        'read_only_script_sha256': sha(Path(__file__).read_bytes()),
        'additional_Lean_or_Lake_or_kernel_execution': False,
        'new_independent_fresh_replay_or_strict_controls': False,
        'C_input_program_numerical_boolean_degree338_proved_at_fixed_commit': False,
        'C_readActions_degree73_proved_at_fixed_commit': True,
        'E_actual_binary_generation_provider_and_numeric_records_bound': True,
        'E_fixed_program_integrates_C_input_reference_path': False,
        'whole_machine_bit_time_proved': False,
        'new_major_novelty_claim': False,
    }

if __name__ == '__main__':
    expected = json.loads((HERE / 'MANIFEST.json').read_text())
    actual = gather()
    assert actual == expected, 'Manifest mismatch'
    print(json.dumps({'status': actual['status'], 'manifest_sha256': sha((HERE / 'MANIFEST.json').read_bytes()),
                      'C_local_modules': len(actual['C_import_binding']['local_modules']),
                      'E_local_modules': len(actual['E_import_binding']['local_modules']),
                      'C_configs': len(actual['C_import_binding']['package_configurations']),
                      'E_configs': len(actual['E_import_binding']['package_configurations']),
                      'bound_author_runs': len(actual['author_evidence']),
                      'additional_Lean_or_Lake_or_kernel_execution': False}, indent=2))
