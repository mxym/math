#!/usr/bin/env python3
"""Offline standard-library verification, with package-relative inputs.

The default runs ordinary and optimized Python. Reports are temporary unless
--report is given. No supplied certificate or report is overwritten.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def package_file(root, name):
    require(isinstance(name, str) and Path(name).name == name and name not in ('', '.', '..'),
            'Expected a flat package filename: ' + str(name))
    path = root / name
    require(path.is_file(), 'Missing package file: ' + name)
    return path


def check_rows(root, rows, label):
    seen = set()
    for row in rows:
        name = row['path']
        require(name not in seen, 'Duplicate ' + label + ' entry: ' + name)
        seen.add(name)
        path = package_file(root, name)
        require(type(row['bytes']) is int and path.stat().st_size == row['bytes'],
                label + ' byte count mismatch: ' + name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == row['sha256'],
                label + ' SHA-256 mismatch: ' + name)
    return len(seen)


def check_source_segments(root, rows, functions):
    cached = {}
    for row in rows:
        if row['path'] not in cached:
            source = package_file(root, row['path']).read_text()
            cached[row['path']] = source, ast.parse(source)
        source, tree = cached[row['path']]
        matches = []
        for node in tree.body:
            if functions and isinstance(node, ast.FunctionDef) and node.name == row['name']:
                matches.append(node)
            elif not functions and isinstance(node, ast.Assign):
                if any(isinstance(t, ast.Name) and t.id == row['name'] for t in node.targets):
                    matches.append(node)
        require(len(matches) == 1, 'Missing or duplicated protected source: ' + row['name'])
        segment = ast.get_source_segment(source, matches[0])
        require(hashlib.sha256(segment.encode()).hexdigest() == row['sha256_source_segment'],
                'Original arithmetic changed: ' + row['path'] + ':' + row['name'])
    return len(rows)


def integrity(root, skip_manifest):
    mapping = json.loads(package_file(root, 'SOURCE_MAP.json').read_text())
    candidate = json.loads(package_file(root, 'CANDIDATE_ID.json').read_text())
    require(mapping['schema'] == 1, 'Unsupported source-map schema.')
    require(mapping['immutable_candidate']['sha256'] == candidate['immutable_candidate_sha256'],
            'Immutable candidate SHA identifiers disagree.')
    require(mapping['immutable_candidate']['archive_name'] == candidate['immutable_candidate_filename'],
            'Immutable archive names disagree.')
    count = check_rows(root, mapping['protected_candidate_files'], 'Immutable input')
    functions = check_source_segments(root, mapping['protected_function_sources'], True)
    constants = check_source_segments(root, mapping['protected_constant_sources'], False)
    manifest_count = None
    if not skip_manifest:
        manifest = json.loads(package_file(root, 'MANIFEST.json').read_text())
        require(manifest['schema'] == 1, 'Unsupported publication-manifest schema.')
        manifest_count = check_rows(root, manifest['files'], 'Publication manifest')
    print('PASS: original certificate/input bytes and protected arithmetic source.', flush=True)
    print('PASS: publication manifest.' if not skip_manifest else
          'Assembly mode: publication manifest intentionally not checked.', flush=True)
    return {'immutable_candidate_sha256': mapping['immutable_candidate']['sha256'],
            'protected_files': count, 'protected_arithmetic_functions': functions,
            'protected_constants': constants, 'publication_manifest_files': manifest_count}


def run_child(root, directory, python, checker, arguments):
    environment = dict(os.environ)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    result = subprocess.run(python + [str(package_file(root, checker))] + arguments,
                            cwd=directory, env=environment, text=True, capture_output=True)
    require(result.returncode == 0, checker + ' failed:\n' + result.stdout + result.stderr)
    return result.stdout


def replay(root, modes):
    outputs, summary = {}, {}
    with tempfile.TemporaryDirectory(prefix='mixed-envelope-replay-') as directory:
        directory = Path(directory)
        for mode in modes:
            python = [sys.executable] + (['-O'] if mode == 'optimized' else [])
            paths = [directory / (name + '_' + mode + '.json') for name in ('finite', 'tail', 'classical')]
            finite, tail, classical = paths
            run_child(root, directory, python, 'check_finite.py', ['--quiet', '--report', str(finite)])
            run_child(root, directory, python, 'check_mixed_tail.py', ['--report', str(tail)])
            large = run_child(root, directory, python, 'check_mixed_large_dimensions.py', [])
            run_child(root, directory, python, 'check_classical_upper.py', ['--output', str(classical)])
            fd, td, cd = [json.loads(path.read_text()) for path in paths]
            for data, reference in [(fd, 'finite_report.json'), (td, 'mixed_tail_report.json'),
                                    (cd, 'classical_upper_exact.json')]:
                require(data == json.loads(package_file(root, reference).read_text()),
                        'Exact replay differs from supplied report: ' + reference)
            outputs[mode] = tuple(path.read_bytes() for path in paths) + (large,)
            summary[mode] = {'finite_rectangles': fd['rectangles'], 'finite_margin': fd['uniform_upper_margin'],
                             'tail_cells': td['cells'], 'tail_maximum_depth': td['maximum_depth'],
                             'tail_margin': td['uniform_certified_upper_margin'],
                             'tail_certificate_sha256': td['certificate_sha256'],
                             'large_factor_analytic_constants': 'PASS', 'classical_context_constants': 'PASS',
                             'replay_matches_supplied_reports': True}
            print('PASS: all exact checkers from an unrelated working directory (' + mode + ').', flush=True)
    if len(modes) == 2:
        require(outputs['ordinary'] == outputs['optimized'], 'Ordinary and optimized exact outputs differ.')
        print('PASS: ordinary and optimized reports are byte-identical.', flush=True)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('both', 'ordinary', 'optimized'), default='both')
    parser.add_argument('--report', type=Path, help='Optional verification-summary JSON output.')
    parser.add_argument('--integrity-only', action='store_true', help='Check integrity without mathematical replay.')
    parser.add_argument('--skip-publication-manifest', action='store_true',
                        help='Assembly only: the final publication manifest is still pending.')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    checked = integrity(root, args.skip_publication_manifest)
    modes = ['ordinary', 'optimized'] if args.mode == 'both' else [args.mode]
    results = {} if args.integrity_only else replay(root, modes)
    report = {'status': 'PASS', 'integrity': checked, 'mathematics_replayed': not args.integrity_only,
              'replay': results, 'scope': 'Finite products and joins from a point; invertible affine maps on affine hulls.',
              'upper_conclusion': 'Gamma_C <= exp(1049/1000) < 2.855' if results else None,
              'inherited_lower_endpoint': 'Prior Theorem 9.2 and Corollary 9.3; historical replay retained, not rerun here.',
              'network_or_checkout_required': False}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
