#!/usr/bin/env python3
"""Read-only fixed-object/log recheck of the separately appended native bridge.
No Lean, Lake, compiler, Git mutation, or output write is performed.
"""
from pathlib import Path
import json
import posixpath
import re
import runpy

HERE = Path(__file__).resolve().parent
BASELINE = runpy.run_path(str(HERE / 'recheck.py'))
git, blob, sha, record = [BASELINE[x] for x in ['git', 'blob', 'sha', 'record']]
COMMIT = '71147d7005d4315fb5439e36138d24482c794c30'
PARENT = 'fb92b813b71f51f77083714c086c12369f049eb5'
PREFIX = 'formalizations/extraction-rational-gate-binary'
PROVIDER_SHA = 'fa0306e1fb07e4f71481943b402331b5ea6a876027f7ce2b08ecbac04988677c'
BASELINE_MANIFEST_SHA = '512260dc06784f384c2799c8659a1dd41258f3724f7b7f582c5d2fab46768016'

def no_comments(text):
    # Lean nested block comments; sufficient to parse actual source imports.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            out.extend('  ')
            i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            if j == -1:
                break
            out.append('\n')
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    assert depth == 0, 'Unclosed block comment'
    return ''.join(out)

def gather_binary():
    baseline = json.loads((HERE / 'MANIFEST.json').read_text())
    assert sha((HERE / 'MANIFEST.json').read_bytes()) == BASELINE_MANIFEST_SHA
    assert BASELINE['gather']() == baseline
    report_path = PREFIX + '/verification/binary-provider-standard-20261019/REPORT.json'
    report = json.loads(blob(COMMIT, report_path))
    BASELINE['check_snapshot'](COMMIT, report['source_snapshot'])
    assert sha(blob(COMMIT, PREFIX + '/RationalGateBinary/Provider.lean')) == PROVIDER_SHA
    all_paths = set(git('ls-tree', '-r', '--name-only', COMMIT).decode().splitlines())
    manifest = json.loads(blob(COMMIT, PREFIX + '/lake-manifest.json'))
    roots = [PREFIX] + [posixpath.normpath(PREFIX + '/' + p['dir'])
                        for p in manifest['packages'] if p['type'] == 'path']
    assert len(roots) == len(set(roots))
    module_paths = {}
    for root in roots:
        for path in all_paths:
            if path.startswith(root + '/') and path.endswith('.lean') and '/.lake/' not in path:
                relative = path[len(root)+1:]
                if relative == 'lakefile.lean':
                    continue
                module = relative[:-5].replace('/', '.')
                module_paths.setdefault(module, []).append(path)
    visited, external, todo = {}, set(), ['RationalGateBinary.Check']
    while todo:
        module = todo.pop()
        if module in visited:
            continue
        matches = module_paths.get(module, [])
        assert len(matches) == 1, ('ambiguous_or_unresolved_local_module', module, matches)
        path = matches[0]
        text = no_comments(blob(COMMIT, path).decode())
        imports = []
        for line in text.splitlines():
            match = re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+)$', line)
            if match:
                imports.extend(match.group(1).split())
        visited[module] = {**record(COMMIT, path), 'imports': imports}
        for imported in imports:
            if imported in module_paths:
                todo.append(imported)
            else:
                assert imported.split('.')[0] in ['Mathlib', 'Lean', 'Std', 'Batteries', 'Qq', 'Aesop'], ('unresolved_import', imported)
                external.add(imported)
    configs = []
    for root in roots:
        for name in ['lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
            path = root + '/' + name
            if path in all_paths:
                configs.append(record(COMMIT, path))
    package = [record(COMMIT, p) for p in sorted(all_paths) if p.startswith(PREFIX + '/')]
    changed = git('diff', '--name-only', PARENT, COMMIT).decode().splitlines()
    assert set(changed) == {x['path'] for x in package}, 'Changes outside new package'
    # These previously reviewed source prefixes are unchanged at the new seal.
    assert not git('diff', '--name-only', BASELINE['US'], COMMIT, BASELINE['UP'])
    assert not git('diff', '--name-only', BASELINE['P'], COMMIT, BASELINE['PP'])
    assert not git('diff', '--name-only', BASELINE['I'], COMMIT, BASELINE['IP'])
    logs, texts = [], {}
    for name, expected in report['logs'].items():
        path = BASELINE['LOGDIR'] / name
        data = path.read_bytes()
        assert sha(data) == expected, ('binary_log_hash', name)
        logs.append({'path': str(path), 'bytes': len(data), 'sha256': sha(data)})
        texts[name] = data.decode()
    standard = texts['20261018T223454910161Z-extraction-rational-gate-binary.log']
    check = texts['20261018T223443816684Z-root-owned-RationalGateBinary.Check.log']
    assert 'Build completed successfully (3963 jobs).' in standard
    for text in [standard, check]:
        assert 'CONCRETE_NATIVE_WORD_PROVIDER_CHECK_PASS' in text
    for decl, expected in report['axioms'].items():
        match = re.search(r"'" + re.escape(decl) + r"' depends on axioms: \[([^]]*)\]", check, re.S)
        assert match, ('binary_axiom_text_missing', decl)
        actual = re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', match.group(1))
        assert sorted(actual) == sorted(expected), ('binary_axiom_drift', decl, actual)
    selected = blob(COMMIT, PREFIX + '/ROOTS.txt').decode().splitlines()
    assert selected == list(report['axioms']) and len(selected) == 8
    reviewed_deps = [
        'NativeBinaryPacketInput.lean', 'NativeCachedSynthesis.lean', 'NativeWordEvaluation.lean',
        'CanonicalBinaryWords.lean', 'SignedBinaryWords.lean', 'WordPacketMultiplication.lean',
        'IntegerPackets.lean', 'NativePacketCache.lean', 'BinaryWordAddition.lean',
    ]
    return {
        'status': 'BINARY_BRIDGE_FIXED_GIT_SOURCE_LOG_AND_IMPORT_BINDING_READ_ONLY_PASS',
        'fixed_binary_commit': COMMIT, 'parent_commit': PARENT,
        'provider_source_sha256': PROVIDER_SHA,
        'initial_review_manifest_sha256': BASELINE_MANIFEST_SHA,
        'package_entries': package,
        'directly_reviewed_dependencies': [record(COMMIT, 'formalizations/extraction-numerical-synthesis/CircuitNumerical/' + n) for n in reviewed_deps],
        'independently_resolved_local_import_closure': dict(sorted(visited.items())),
        'external_import_names': sorted(external),
        'reachable_package_configurations': configs,
        'original_author_logs': logs,
        'selected_roots': selected,
        'author_standard_build_jobs': 3963,
        'actual_log_types_axioms_and_small_data_markers_checked': True,
        'all_changes_since_parent_confined_to_new_binary_package': True,
        'prior_three_package_prefixes_unchanged_at_new_seal': True,
        'binary_appendix_sha256': sha((HERE / 'BINARY_APPENDIX.md').read_bytes()),
        'binary_read_only_recheck_script_sha256': sha(Path(__file__).read_bytes()),
        'additional_Lean_or_Lake_or_kernel_execution': False,
        'independent_empty_kernel_or_controls': False,
        'whole_provider_or_compiler_machine_time_proved': False,
    }

if __name__ == '__main__':
    expected = json.loads((HERE / 'BINARY_MANIFEST.json').read_text())
    actual = gather_binary()
    assert actual == expected, 'Binary manifest mismatch'
    print(json.dumps({'status': actual['status'],
                      'binary_manifest_sha256': sha((HERE / 'BINARY_MANIFEST.json').read_bytes()),
                      'package_files': len(actual['package_entries']),
                      'closure_modules': len(actual['independently_resolved_local_import_closure']),
                      'package_configs': len(actual['reachable_package_configurations']),
                      'author_logs': len(actual['original_author_logs']),
                      'additional_Lean_or_Lake_or_kernel_execution': False}, indent=2))
