#!/usr/bin/env python3
"""Packaging mutation controls, including normal and Python -O entry points.

Mutates isolated temporary copies only. No Lean, dependency, or network work.
Must start from a valid sealed package. Write reports outside the source tree.
"""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
sys.dont_write_bytecode = True
from release_integrity import (ARCHIVE_PREFIX, EXPECTED_FILES, METADATA, RUNTIME_DIRECTORIES,
                               ReleaseIntegrityError, checksum_bytes, require, sha256, validated_snapshot)
ROOT = Path(__file__).resolve().parents[1]
PROOF = 'project/ContinuumRemainder/FinalProof.lean'
PIN = 'project/lake-manifest.json'
PROBE = 'audit/checks/ExactMain.lean'
LEDGER = 'provenance/PUBLIC_DERIVATIVE_LEDGER.json'
ORIGINAL = 'provenance/ORIGINAL_SOURCE_SHA256.json'


def change(root, name, transform):
    path = root / name
    path.write_text(transform(path.read_text()))


def json_change(root, name, transform):
    path = root / name
    value = json.loads(path.read_text())
    transform(value)
    path.write_text(json.dumps(value, indent=2) + '\n')


def outer_rehash(root):
    """Deliberately hostile resealing of current outer entries, not a public API."""
    path = root / 'SOURCE_MANIFEST.json'
    manifest = json.loads(path.read_text())
    manifest['sha256'] = {name: sha256((root / name).read_bytes()) for name in manifest['sha256']}
    path.write_text(json.dumps(manifest, indent=2) + '\n')
    hashes = dict(manifest['sha256'])
    hashes['SOURCE_MANIFEST.json'] = sha256(path.read_bytes())
    (root / 'SHA256SUMS').write_bytes(checksum_bytes(hashes))


def corrupt_and_rehash(root, name):
    with (root / name).open('ab') as stream:
        stream.write(b'\n')
    outer_rehash(root)


def coordinated_source_rewrite(root):
    change(root, PROOF, lambda text: text + '\n-- changed proof input\n')
    digest = sha256((root / PROOF).read_bytes())
    json_change(root, ORIGINAL, lambda data: data.__setitem__(PROOF, digest))
    def update(ledger):
        for row in ledger:
            if row['public'] == PROOF:
                row['original_sha256'] = row['public_sha256'] = digest
    json_change(root, LEDGER, update)
    outer_rehash(root)


def erase_from_every_outer_record(root, name):
    (root / name).unlink()
    json_change(root, 'SOURCE_MANIFEST.json', lambda data: data['sha256'].pop(name))
    outer_rehash(root)


def source_symlink(root):
    (root / PROBE).unlink()
    (root / PROBE).symlink_to('ReplayClosure.lean')


def directory_symlink(root):
    (root / 'audit/checks').rename(root / 'saved-checks')
    (root / 'audit/checks').symlink_to('../../saved-checks', target_is_directory=True)


def runtime_symlink(root, path):
    (root / path).symlink_to('audit' if '/' not in path else '../audit', target_is_directory=True)


def allowed_runtime(root):
    for name in RUNTIME_DIRECTORIES:
        path = root / name
        path.mkdir()
        (path / 'generated.txt').write_text('Generated files are not frozen release inputs.\n')


def mutate_ledger_and_rehash(root):
    json_change(root, LEDGER, lambda rows: rows.pop())
    outer_rehash(root)


def add_manifest_member(root, path):
    json_change(root, 'SOURCE_MANIFEST.json', lambda data: data['sha256'].__setitem__(path, '0' * 64))


def cases():
    result = {
        'baseline': (lambda root: None, True),
        'documented_runtime_directories': (allowed_runtime, True),
        'manifest_missing': (lambda root: (root / 'SOURCE_MANIFEST.json').unlink(), False),
        'checksums_missing': (lambda root: (root / 'SHA256SUMS').unlink(), False),
        'both_seal_records_missing': (lambda root: [(root / name).unlink() for name in ('SOURCE_MANIFEST.json', 'SHA256SUMS')], False),
        'manifest_malformed': (lambda root: (root / 'SOURCE_MANIFEST.json').write_text('{'), False),
        'manifest_excessive_nesting': (lambda root: (root / 'SOURCE_MANIFEST.json').write_text('[' * 2000 + ']' * 2000), False),
        'manifest_nonfinite_number': (lambda root: change(root, 'SOURCE_MANIFEST.json', lambda text: text.replace('"format": 2', '"format": NaN', 1)), False),
        'manifest_top_level_array': (lambda root: (root / 'SOURCE_MANIFEST.json').write_text('[]'), False),
        'duplicate_manifest_key': (lambda root: change(root, 'SOURCE_MANIFEST.json', lambda text: text.replace('"format": 2,', '"format": 2, "format": 2,', 1)), False),
        'duplicate_member_key': (lambda root: change(root, 'SOURCE_MANIFEST.json', lambda text: text.replace('"sha256": {', '"sha256": {"' + PROBE + '": "' + '0' * 64 + '",', 1)), False),
        'manifest_unknown_field': (lambda root: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data.__setitem__('unknown', 0)), False),
        'manifest_hashes_array': (lambda root: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data.__setitem__('sha256', [])), False),
        'manifest_format_boolean': (lambda root: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data.__setitem__('format', True)), False),
        'manifest_hash_invalid': (lambda root: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data['sha256'].__setitem__(PROBE, 'wrong')), False),
        'manifest_hash_nonstring': (lambda root: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data['sha256'].__setitem__(PROBE, 1)), False),
        'manifest_hash_uppercase': (lambda root: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data['sha256'].__setitem__(PROBE, 'A' * 64)), False),
        'manifest_hash_wrong': (lambda root: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data['sha256'].__setitem__(PROBE, '0' * 64)), False),
        'manifest_member_missing': (lambda root: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data['sha256'].pop(PROBE)), False),
        'manifest_whitespace_stale_binding': (lambda root: change(root, 'SOURCE_MANIFEST.json', lambda text: text + '\n'), False),
        'checksum_corrupt': (lambda root: (root / 'SHA256SUMS').write_text('invalid\n'), False),
        'checksum_wrong_digest': (lambda root: change(root, 'SHA256SUMS', lambda text: '0' * 64 + text[64:]), False),
        'checksum_omitted_row': (lambda root: change(root, 'SHA256SUMS', lambda text: ''.join(text.splitlines(True)[1:])), False),
        'checksum_duplicate_row': (lambda root: change(root, 'SHA256SUMS', lambda text: text + text.splitlines(True)[0]), False),
        'checksum_order_changed': (lambda root: change(root, 'SHA256SUMS', lambda text: ''.join(reversed(text.splitlines(True)))), False),
        'proof_bytes_changed': (lambda root: change(root, PROOF, lambda text: text + '\n-- changed\n'), False),
        'proof_outer_rehashed': (lambda root: corrupt_and_rehash(root, PROOF), False),
        'pin_outer_rehashed': (lambda root: corrupt_and_rehash(root, PIN), False),
        'toolchain_outer_rehashed': (lambda root: corrupt_and_rehash(root, 'project/lean-toolchain'), False),
        'source_freeze_outer_rehashed': (lambda root: corrupt_and_rehash(root, 'submitted-evidence/source-freeze.json'), False),
        'original_map_outer_rehashed': (lambda root: corrupt_and_rehash(root, ORIGINAL), False),
        'dependency_metadata_outer_rehashed': (lambda root: corrupt_and_rehash(root, 'provenance/DEPENDENCY_PROVENANCE.json'), False),
        'input_archive_metadata_outer_rehashed': (lambda root: corrupt_and_rehash(root, 'provenance/INPUT_ARCHIVE.json'), False),
        'license_outer_rehashed': (lambda root: corrupt_and_rehash(root, 'third_party_licenses/mathlib/LICENSE'), False),
        'license_checksums_outer_rehashed': (lambda root: corrupt_and_rehash(root, 'third_party_licenses/SHA256SUMS'), False),
        'public_probe_outer_rehashed': (lambda root: corrupt_and_rehash(root, PROBE), False),
        'audit_report_outer_rehashed': (lambda root: corrupt_and_rehash(root, 'audit/independent/FINAL_AUDIT.json'), False),
        'ledger_outer_rehashed': (mutate_ledger_and_rehash, False),
        'coordinated_source_provenance_rewrite': (coordinated_source_rewrite, False),
        'unlisted_source_file': (lambda root: (root / 'project/Unlisted.lean').write_text('import Mathlib\n'), False),
        'unlisted_script': (lambda root: (root / 'scripts/unlisted.py').write_text('print(1)\n'), False),
        'unlisted_empty_directory': (lambda root: (root / 'unlisted').mkdir(), False),
        'unlisted_nested_runtime': (lambda root: (root / 'audit/.lake').mkdir(), False),
        'manifest_symlink': (lambda root: ((root / 'SOURCE_MANIFEST.json').unlink(), (root / 'SOURCE_MANIFEST.json').symlink_to('README.md')), False),
        'checksum_symlink': (lambda root: ((root / 'SHA256SUMS').unlink(), (root / 'SHA256SUMS').symlink_to('README.md')), False),
        'declared_source_symlink': (source_symlink, False),
        'declared_directory_symlink': (directory_symlink, False),
        'unlisted_symlink': (lambda root: (root / 'unlisted').symlink_to('README.md'), False),
        'non_regular_fifo': (lambda root: os.mkfifo(root / 'fifo'), False),
    }
    for key in METADATA:
        result['metadata_missing_' + key] = (lambda root, key=key: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data.pop(key)), False)
        result['metadata_altered_' + key] = (lambda root, key=key: json_change(root, 'SOURCE_MANIFEST.json', lambda data: data.__setitem__(key, 'incorrect')), False)
    for name in [PROBE, PROOF, PIN, ORIGINAL, LEDGER, 'submitted-evidence/source-freeze.json',
                 'third_party_licenses/mathlib/LICENSE', 'third_party_licenses/lean4/LICENSES',
                 'README.md', 'PROVENANCE.md', 'scripts/verify.py', 'scripts/seal_release.py']:
        result['missing_required_' + name.replace('/', '_')] = (lambda root, name=name: erase_from_every_outer_record(root, name), False)
    for path in ['../outside', '/outside', 'audit//Other.lean', 'audit/../Other.lean', 'audit/./Other.lean', 'audit\\Other.lean', 'audit/line\nname']:
        result['unsafe_member_' + repr(path)] = (lambda root, path=path: add_manifest_member(root, path), False)
    for path in RUNTIME_DIRECTORIES:
        result['runtime_symlink_' + path] = (lambda root, path=path: runtime_symlink(root, path), False)
        result['runtime_file_' + path] = (lambda root, path=path: (root / path).write_text('wrong kind\n'), False)
    return result


def copy_snapshot(snapshot, destination):
    for name, data in snapshot.items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def seals(root):
    return {name: ('symlink', os.readlink(root / name)) if (root / name).is_symlink() else
            (root / name).read_bytes() if (root / name).exists() else None
            for name in ('SOURCE_MANIFEST.json', 'SHA256SUMS')}


def execute(root, entry, optimized, arguments):
    return subprocess.run([sys.executable] + (['-O'] if optimized else []) + ['-B', str(root / 'scripts' / (entry + '.py'))] + arguments,
                          text=True, capture_output=True)


def check_archive(path, snapshot):
    raw = path.read_bytes()
    require(raw[:4] == b'\x1f\x8b\x08\x00' and raw[4:8] == b'\0' * 4,
            'archive gzip timestamp or optional header differs')
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as archive:
        members = archive.getmembers()
        require([member.name for member in members] == [ARCHIVE_PREFIX + '/' + name for name in sorted(snapshot)],
                'archive member layout differs')
        for member, (name, data) in zip(members, sorted(snapshot.items())):
            require(member.isfile() and member.mode == 0o644 and member.mtime == 0 and
                    member.uid == member.gid == 0 and member.uname == member.gname == '',
                    'archive ownership/mode/time/type differs: ' + name)
            require(archive.extractfile(member).read() == data, 'archive bytes differ: ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT), 'regression report must be outside the source tree')
    snapshot = validated_snapshot(ROOT)
    rows = []
    all_cases = cases()
    for case, (mutate, accept) in all_cases.items():
        with tempfile.TemporaryDirectory(prefix='continuum-integrity-') as temporary:
            work = Path(temporary)
            copy = work / 'source'
            copy_snapshot(snapshot, copy)
            mutate(copy)
            before = seals(copy)
            for optimized in (False, True):
                for entry in ('verify_integrity', 'make_archive', 'verify'):
                    if entry == 'verify' and not (copy / 'scripts/verify.py').exists():
                        continue  # The other two guards reject a missing build entry point.
                    archive = work / (entry + ('-O' if optimized else '') + '.tar.gz')
                    arguments = [] if entry == 'verify_integrity' else ['--output', str(archive)]
                    build_output = work / ('unused-build-O' if optimized else 'unused-build-normal')
                    if entry == 'verify':
                        arguments = ['--lean-bin', str(work / 'MISSING'), '--dependency-project', str(work / 'MISSING'),
                                     '--output', str(build_output)]
                    result = execute(copy, entry, optimized, arguments)
                    log = result.stdout + result.stderr
                    if accept:
                        passed = result.returncode == 0 and (entry != 'verify_integrity' or 'RELEASE_INTEGRITY_PASS' in log)
                        if entry == 'verify':
                            passed = result.returncode != 0 and 'install exact toolchain and use --lean-bin' in log and not build_output.exists()
                        if entry == 'make_archive' and passed:
                            check_archive(archive, snapshot)
                    else:
                        passed = result.returncode != 0 and 'RELEASE_INTEGRITY:' in log and not archive.exists() and not build_output.exists()
                    require(passed, 'control failed: ' + case + ' ' + entry + (' -O' if optimized else '') + '\n' + log)
                    require(seals(copy) == before, 'entry point rewrote seal records: ' + case)
                    rows.append({'case': case, 'entry_point': entry, 'optimized': optimized,
                                 'expected': 'accept' if accept else 'reject_before_archive',
                                 'returncode': result.returncode, 'passed': True})
    # Explicit maintainer sealing is separate and cannot rewrite an existing seal.
    for optimized in (False, True):
        for kind, accept in [('valid_unsealed', True), ('existing_seal', False),
                             ('one_existing_seal', False), ('mutated_source', False), ('missing_license', False)]:
            with tempfile.TemporaryDirectory(prefix='continuum-seal-') as temporary:
                copy = Path(temporary) / 'source'
                copy_snapshot(snapshot, copy)
                if kind != 'existing_seal':
                    (copy / 'SHA256SUMS').unlink()
                    if kind != 'one_existing_seal':
                        (copy / 'SOURCE_MANIFEST.json').unlink()
                if kind == 'mutated_source':
                    change(copy, PROOF, lambda text: text + '\n-- changed\n')
                if kind == 'missing_license':
                    (copy / 'third_party_licenses/mathlib/LICENSE').unlink()
                before = seals(copy)
                result = execute(copy, 'seal_release', optimized, ['--initialize'])
                log = result.stdout + result.stderr
                require((result.returncode == 0 and 'RELEASE_SEAL_INITIALIZED' in log) if accept else
                        (result.returncode != 0 and 'RELEASE_INTEGRITY:' in log and seals(copy) == before),
                        'maintainer seal control failed: ' + kind + '\n' + log)
                if accept:
                    require(seals(copy) == {name: snapshot[name] for name in before}, 'seal initialization is not deterministic')
                rows.append({'case': kind, 'entry_point': 'seal_release', 'optimized': optimized,
                             'expected': 'accept' if accept else 'reject_without_reseal', 'passed': True,
                             'returncode': result.returncode})
    # Stable bytes under repeated runs and Python -O, including different file mtimes.
    with tempfile.TemporaryDirectory(prefix='continuum-determinism-') as temporary:
        work = Path(temporary)
        copy = work / 'source'
        copy_snapshot(snapshot, copy)
        outputs = []
        for iteration, optimized in enumerate((False, False, True)):
            for name in snapshot:
                os.utime(copy / name, (1111111111 + iteration, 1111111111 + iteration))
            output_archive = work / ('deterministic-' + str(iteration) + '.tar.gz')
            result = execute(copy, 'make_archive', optimized, ['--output', str(output_archive)])
            require(result.returncode == 0, 'deterministic archive control failed: ' + result.stderr)
            check_archive(output_archive, snapshot)
            outputs.append(output_archive.read_bytes())
        require(outputs[0] == outputs[1] == outputs[2], 'archive bytes are not deterministic')
        # Round-trip only validated regular members into a new root, without tar extraction helpers.
        extracted = work / 'extracted'
        with tarfile.open(fileobj=io.BytesIO(outputs[0]), mode='r:gz') as archive:
            for member in archive.getmembers():
                destination = extracted / member.name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(archive.extractfile(member).read())
        for optimized in (False, True):
            result = execute(extracted / ARCHIVE_PREFIX, 'verify_integrity', optimized, [])
            require(result.returncode == 0 and 'RELEASE_INTEGRITY_PASS' in result.stdout,
                    'extracted archive integrity check failed: ' + result.stderr)
        # Output containment and output-symlink guards must reject before writing.
        target = work / 'symlink-target'
        target.write_bytes(b'outside target')
        link = work / 'linked-output.tar.gz'
        link.symlink_to(target.name)
        for optimized in (False, True):
            for archive_path in (copy / 'forbidden.tar.gz', link):
                result = execute(copy, 'make_archive', optimized, ['--output', str(archive_path)])
                require(result.returncode != 0 and 'RELEASE_INTEGRITY:' in result.stdout + result.stderr,
                        'unsafe archive output was accepted')
            require(not (copy / 'forbidden.tar.gz').exists() and link.is_symlink() and
                    target.read_bytes() == b'outside target', 'unsafe output control changed files')
        # A rejected archive operation must preserve any preexisting output.
        marker = work / 'existing.tar.gz'
        marker.write_bytes(b'prior output must survive rejection')
        (copy / 'SOURCE_MANIFEST.json').unlink()
        for optimized in (False, True):
            result = execute(copy, 'make_archive', optimized, ['--output', str(marker)])
            require(result.returncode != 0 and 'RELEASE_INTEGRITY:' in result.stdout + result.stderr and
                    marker.read_bytes() == b'prior output must survive rejection', 'invalid archive overwrote existing output')
    report = {
        'status': 'PASS', 'scope': 'Packaging integrity controls, not mathematical proof tests',
        'case_count': len(all_cases), 'production_invocations': len(rows) + 11,
        'positive_cases': sum(accept for _, accept in all_cases.values()),
        'negative_cases': sum(not accept for _, accept in all_cases.values()),
        'normal_and_optimized_entry_points_exercised': True,
        'archive_bytes_match_across_repeated_runs_mtimes_and_python_optimization': True,
        'extracted_archive_verifies_normal_and_optimized': True,
        'archive_output_containment_and_symlink_controls': True,
        'archive_member_bytes_types_prefix_ownership_modes_and_times_verified': True,
        'archive_entry_point_does_not_reseal': True, 'build_entry_point_rejects_before_lean_or_output_creation': True, 'sealing_requires_explicit_initialization': True,
        'no_lean_or_network_execution': True,
        'authenticity_limit': 'Trust an external archive digest or commit; self-consistent rewriting of the validator and all records is outside this check.',
        'results': rows,
    }
    output.write_text(json.dumps(report, indent=2) + '\n')
    print('PACKAGING_GUARD_CONTROLS_PASS ' + str(report['production_invocations']) + ' production invocations')


if __name__ == '__main__':
    try:
        main()
    except (ReleaseIntegrityError, OSError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
