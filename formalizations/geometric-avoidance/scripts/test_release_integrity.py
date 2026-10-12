#!/usr/bin/env python3
"""Exercise both production integrity entry points normally and under Python -O.
Only temporary copies are mutated. No Lean, network, dependency cache or original
proof source is changed by these packaging regression tests.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
from release_integrity import validate_release

ROOT = Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def change(path, transform):
    path.write_text(transform(path.read_text()))

def manifest_change(root, transform):
    path = root / 'SOURCE_MANIFEST.json'
    data = json.loads(path.read_text())
    transform(data)
    path.write_text(json.dumps(data, indent=2) + '\n')

def omit_and_change_wrapper(root):
    manifest_change(root, lambda data: data['sha256'].pop('checks/ExactMain.lean'))
    (root / 'checks/ExactMain.lean').write_text('import ContinuumGeometric\n')

def omit_and_delete_wrapper(root):
    manifest_change(root, lambda data: data['sha256'].pop('checks/ExactMain.lean'))
    (root / 'checks/ExactMain.lean').unlink()
    change(root / 'SHA256SUMS', lambda text: ''.join(line for line in text.splitlines(True)
                                                    if not line.endswith('  checks/ExactMain.lean\n')))

def source_symlink(root):
    (root / 'checks/ExactMain.lean').unlink()
    (root / 'checks/ExactMain.lean').symlink_to('IndependentBoundaryFacts.lean')

def allowed_runtime(root):
    for name in ('.lake', 'vendor', 'replay-evidence', '.git'):
        path = root / name
        path.mkdir()
        (path / 'generated.txt').write_text('Generated runtime data is outside the source payload.\n')

def rehash_outer_release(root):
    path = root / 'SOURCE_MANIFEST.json'
    data = json.loads(path.read_text())
    data['sha256'] = {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                      for name in data['sha256']}
    path.write_text(json.dumps(data, indent=2) + '\n')
    hashes = dict(data['sha256'])
    hashes['SOURCE_MANIFEST.json'] = hashlib.sha256(path.read_bytes()).hexdigest()
    (root / 'SHA256SUMS').write_text(''.join(digest + '  ' + name + '\n'
                                           for name, digest in sorted(hashes.items())))

def mutate_then_rehash(root, kind):
    if kind == 'proof':
        change(root / 'ContinuumGeometric/MainProof.lean', lambda text: text + '\n-- changed\n')
    elif kind == 'pin':
        change(root / 'lake-manifest.json', lambda text: text.replace('d13f23b723b8a846827a245b89c10fc7d3f11612', '0' * 40))
    elif kind == 'original_inventory':
        path = root / 'provenance/ORIGINAL_SOURCE_SHA256.json'
        data = json.loads(path.read_text())
        data.pop('ContinuumGeometric/Target.lean')
        path.write_text(json.dumps(data, indent=2) + '\n')
    elif kind == 'exact_probe':
        (root / 'checks/ExactMain.lean').write_text('import ContinuumGeometric\n')
    elif kind == 'wrapper_ledger':
        path = root / 'provenance/CHECK_WRAPPER_PROVENANCE.json'
        data = json.loads(path.read_text())
        data.pop()
        path.write_text(json.dumps(data, indent=2) + '\n')
    else:
        raise RuntimeError('Unknown mutation')
    rehash_outer_release(root)

CASES = {
    'baseline': (lambda root: None, True),
    'proof_changed_outer_manifest_rehashed': (lambda root: mutate_then_rehash(root, 'proof'), False),
    'pin_changed_outer_manifest_rehashed': (lambda root: mutate_then_rehash(root, 'pin'), False),
    'original_inventory_omitted_outer_rehashed': (lambda root: mutate_then_rehash(root, 'original_inventory'), False),
    'exact_probe_changed_outer_rehashed': (lambda root: mutate_then_rehash(root, 'exact_probe'), False),
    'wrapper_ledger_omitted_outer_rehashed': (lambda root: mutate_then_rehash(root, 'wrapper_ledger'), False),
    'documented_runtime_directories': (allowed_runtime, True),
    'manifest_missing': (lambda root: (root / 'SOURCE_MANIFEST.json').unlink(), False),
    'checksums_missing': (lambda root: (root / 'SHA256SUMS').unlink(), False),
    'manifest_malformed': (lambda root: (root / 'SOURCE_MANIFEST.json').write_text('{\n'), False),
    'duplicate_manifest_key': (lambda root: change(root / 'SOURCE_MANIFEST.json', lambda text: text.replace('"format": 1,', '"format": 1, "format": 1,', 1)), False),
    'duplicate_member_key': (lambda root: change(root / 'SOURCE_MANIFEST.json', lambda text: text.replace('"sha256": {', '"sha256": {"checks/ExactMain.lean": "' + '0' * 64 + '",', 1)), False),
    'manifest_entry_omitted_wrapper_changed': (omit_and_change_wrapper, False),
    'manifest_entry_and_wrapper_deleted': (omit_and_delete_wrapper, False),
    'wrapper_bytes_changed': (lambda root: (root / 'checks/ExactMain.lean').write_text('import ContinuumGeometric\n'), False),
    'source_archive_identity_changed': (lambda root: manifest_change(root, lambda data: data.__setitem__('source_archive_sha256', '0' * 64)), False),
    'format_type_changed': (lambda root: manifest_change(root, lambda data: data.__setitem__('format', True)), False),
    'scope_changed': (lambda root: manifest_change(root, lambda data: data.__setitem__('scope', 'Different theorem')), False),
    'unknown_schema_field': (lambda root: manifest_change(root, lambda data: data.__setitem__('unknown', 'field')), False),
    'manifest_digest_changed': (lambda root: manifest_change(root, lambda data: data['sha256'].__setitem__('checks/ExactMain.lean', '0' * 64)), False),
    'manifest_digest_malformed': (lambda root: manifest_change(root, lambda data: data['sha256'].__setitem__('checks/ExactMain.lean', 'not-a-hash')), False),
    'traversal_member': (lambda root: manifest_change(root, lambda data: data['sha256'].__setitem__('../outside', '0' * 64)), False),
    'absolute_member': (lambda root: manifest_change(root, lambda data: data['sha256'].__setitem__('/outside', '0' * 64)), False),
    'noncanonical_member': (lambda root: manifest_change(root, lambda data: data['sha256'].__setitem__('checks//Other.lean', '0' * 64)), False),
    'checksum_text_corrupt': (lambda root: (root / 'SHA256SUMS').write_text('not a valid checksum list\n'), False),
    'checksum_digest_changed': (lambda root: change(root / 'SHA256SUMS', lambda text: '0' * 64 + text[64:]), False),
    'checksum_row_missing': (lambda root: change(root / 'SHA256SUMS', lambda text: ''.join(text.splitlines(True)[1:])), False),
    'checksum_row_duplicated': (lambda root: change(root / 'SHA256SUMS', lambda text: text + text.splitlines(True)[0]), False),
    'manifest_checksum_binding_stale': (lambda root: change(root / 'SOURCE_MANIFEST.json', lambda text: text + '\n'), False),
    'unlisted_lean_input': (lambda root: (root / 'checks/Unlisted.lean').write_text('import ContinuumGeometric\n'), False),
    'unlisted_script_input': (lambda root: (root / 'scripts/unlisted.py').write_text('print("not part of the frozen release")\n'), False),
    'declared_source_symlink': (source_symlink, False),
    'proof_bytes_changed': (lambda root: change(root / 'ContinuumGeometric/MainProof.lean', lambda text: text + '\n-- changed\n'), False),
    'dependency_pin_changed': (lambda root: change(root / 'lake-manifest.json', lambda text: text.replace('d13f23b723b8a846827a245b89c10fc7d3f11612', '0' * 40)), False),
}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='Write the regression JSON outside the source project')
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT) or output.is_relative_to(ROOT / 'replay-evidence'), 'Regression report must be outside the source tree or in replay-evidence')
    files = validate_release(ROOT)
    rows = []
    for case, (mutate, accept) in CASES.items():
        with tempfile.TemporaryDirectory(prefix='geometric-integrity-') as temporary:
            work = Path(temporary)
            copy = work / 'source'
            for name in files:
                destination = copy / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / name, destination)
            mutate(copy)
            for optimized in (False, True):
                python = [sys.executable] + (['-O'] if optimized else []) + ['-B']
                for entry in ('reproduce', 'make_archive'):
                    archive = work / (entry + ('-O' if optimized else '') + '.tar.gz')
                    if entry == 'reproduce':
                        command = python + [str(copy / 'scripts/reproduce.py'), '--lean-bin', str(work / 'MISSING'),
                                            '--output', str(work / ('unused-O' if optimized else 'unused-normal'))]
                        if accept:
                            command.append('--verify-release-only')
                    else:
                        command = python + [str(copy / 'scripts/make_archive.py'), str(archive)]
                    result = subprocess.run(command, text=True, capture_output=True)
                    log = result.stdout + result.stderr
                    rejected = result.returncode != 0 and 'RELEASE_INTEGRITY:' in log
                    if accept:
                        passed = result.returncode == 0 and (entry != 'reproduce' or 'RELEASE_INTEGRITY_PASS' in log)
                    else:
                        passed = rejected and not archive.exists()
                    require(passed, 'Integrity regression failed: ' + case + ' ' + entry +
                            (' -O' if optimized else '') + '\n' + log)
                    rows.append({'case': case, 'entry_point': entry, 'optimized': optimized,
                                 'expected': 'accept' if accept else 'reject_before_execution_or_archive',
                                 'returncode': result.returncode, 'passed': True})
    report = {'status': 'PASS', 'scope': 'Packaging integrity controls; not mathematical proof tests',
              'case_count': len(CASES), 'production_invocations': len(rows),
              'positive_cases': sum(accept for _, accept in CASES.values()),
              'negative_cases': sum(not accept for _, accept in CASES.values()),
              'normal_and_optimized_entry_points_exercised': True,
              'no_lean_or_network_execution': True,
              'authenticity_limit': 'Unkeyed internal hashes require an externally trusted archive digest or repository commit; self-consistent adversarial rewriting of the validator and all metadata is outside this integrity check.',
              'results': rows}
    output.write_text(json.dumps(report, indent=2) + '\n')
    print('PACKAGING_GUARD_CONTROLS_PASS ' + str(len(rows)) + ' production invocations')

if __name__ == '__main__':
    main()
