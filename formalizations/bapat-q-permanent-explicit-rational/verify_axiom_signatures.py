#!/usr/bin/env python3
"""Supplemental standard-axiom signature audit; no new mathematical replay."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess

from replay import COMMIT, COMPILER_SHA256

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check-record', action='store_true')
    for name in ['lean', 'dependency-project', 'proof-run', 'original-proof-run',
                 'parameter-proof-run', 'output']:
        p.add_argument('--' + name, type=Path)
    a = p.parse_args()
    if a.check_record:
        rdir = HERE / 'verification/axiom-signatures'
        report = json.loads((rdir / 'report.json').read_text())
        need(report['status'] == 'PASS' and report['negative_controls_rejected'] == 13,
             'Invalid signature record')
        need(report['driver_sha256'] == digest(Path(__file__)), 'Changed signature driver')
        need(report['proof_report_sha256'] == digest(HERE / 'verification/report.json'),
             'Changed proof report')
        for name, h in report['source_sha256'].items():
            need(digest(HERE / name) == h and digest(rdir / name) == h, 'Changed source: ' + name)
        for name, h in report['payload_sha256'].items():
            need(digest(rdir / name) == h, 'Changed signature evidence: ' + name)
        print('STANDARD_AXIOM_SIGNATURE_RECORD_INTEGRITY_PASS; not a new Lean execution')
        return
    need(all(getattr(a, name) is not None for name in [
        'lean', 'dependency_project', 'proof_run', 'original_proof_run',
        'parameter_proof_run', 'output']), 'All execution paths are required')
    lean = a.lean.resolve(strict=True)
    need(digest(lean) == COMPILER_SHA256 and subprocess.check_output(
        [str(lean), '--githash'], text=True).strip() == COMMIT, 'Wrong official compiler')
    run = a.proof_run.resolve(strict=True)
    report_path = run / 'report.json'
    need(digest(report_path) == digest(HERE / 'verification/report.json'), 'Wrong proof run')
    main_report = json.loads(report_path.read_text())
    need(main_report['status'] == 'PASS' and main_report['positive_theorems'] == 30,
         'Proof run did not pass')
    need(digest(run / 'ExplicitBundle.lean') ==
         main_report['generated_source_sha256']['ExplicitBundle.lean'], 'Changed bundle source')
    artifacts = {'ExplicitBundle.olean': run / 'ExplicitBundle.olean'}
    for n, h in main_report['imported_owned_artifact_sha256'].items():
        path = ((a.original_proof_run / 'build' / n.removeprefix('original/'))
                if n.startswith('original/') else
                (a.parameter_proof_run / n.removeprefix('parameter/')))
        need(digest(path) == h, 'Changed proof input: ' + n)
        artifacts[n] = path
    before = {n: digest(path) for n, path in artifacts.items()}
    libs = []
    for name, rev in main_report['package_revisions'].items():
        checkout = a.dependency_project / '.lake/packages' / name
        need(subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'],
                                     text=True).strip() == rev, 'Wrong dependency: ' + name)
        libs.append(checkout / '.lake/build/lib/lean')
    out = a.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    names = ['StandardAxiomGuard.lean', 'CheckLoadedAxioms.lean']
    sources = {n: digest(HERE / n) for n in names}
    for n in names:
        (out / n).write_bytes((HERE / n).read_bytes())
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [out, run, a.parameter_proof_run,
                                                a.original_proof_run / 'build', *libs]))
    env['STANDARD_AXIOM_OUTPUT'] = str(out / 'actual-standard-axioms.json')
    commands = []
    for name, extra in [('StandardAxiomGuard.lean', ['-o', 'StandardAxiomGuard.olean']),
                        ('CheckLoadedAxioms.lean', [])]:
        result = subprocess.run([str(lean), '-j2', '-M6144', *extra, name], cwd=out,
                                env=env, capture_output=True)
        log = Path(name).stem + '.log'
        data = result.stdout + result.stderr
        (out / log).write_bytes(data)
        commands.append({'source': name, 'exit': result.returncode, 'log': log})
        need(result.returncode == 0, 'Signature audit failed: ' + data.decode(errors='replace'))
    need(b'STANDARD_AXIOM_SIGNATURES_PASS; 3 actual declarations; 13 negative controls rejected'
         in data, 'Incomplete signature audit')
    need(before == {n: digest(path) for n, path in artifacts.items()}, 'Changed imported artifacts')
    need(sources == {n: digest(HERE / n) for n in names}, 'Changed checker source')
    result = {'status': 'PASS', 'scope': 'Exact signatures of the three actual standard axioms '
              'loaded with the previously fully replayed explicit Bapat bundle; 13 deliberate '
              'signature/kind/universe/safety mutations rejected. Not another mathematical replay.',
              'source_sha256': sources, 'driver_sha256': digest(Path(__file__)),
              'proof_report_sha256': digest(report_path), 'loaded_artifact_sha256': before,
              'compiler_commit': COMMIT, 'compiler_sha256': COMPILER_SHA256,
              'package_revisions': main_report['package_revisions'], 'commands': commands,
              'negative_controls_rejected': 13,
              'payload_sha256': {n: digest(out / n) for n in [
                  'StandardAxiomGuard.log', 'CheckLoadedAxioms.log', 'actual-standard-axioms.json']}}
    (out / 'report.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('STANDARD_AXIOM_SIGNATURE_AUDIT_PASS; 13 negative controls rejected')


if __name__ == '__main__':
    main()
