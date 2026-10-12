#!/usr/bin/env python3
"""Fresh explicit-witness compilation and full empty-kernel proof replay.

By default also rebuild both already published input proof packages. A pair
of --*-proof-run options reuses completed, source-checked fresh runs, and is
explicitly recorded as input reuse rather than fresh input compilation.
"""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
COMMIT = '5045d0056413266e57c625dcd7c365b10e377c52'
COMPILER_SHA256 = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'


def need(value, message):
    if not value:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def assemble(root):
    modules = json.loads((root / 'MODULES.json').read_text())
    need(len(modules) == len(set(modules)), 'Duplicate module')
    imports, bodies, roots, hashes = [], [], [], {}
    for module in modules:
        path = root / (module + '.lean')
        data = path.read_text()
        hashes[path.name] = digest(path)
        need(not re.search(r'^\s*(?:axiom|unsafe|partial)\b|\bsorry\b|\bnative_decide\b', data, re.M),
             'Admission/unsafe/native proof source: ' + path.name)
        roots.extend('BapatExplicit.' + n for n in re.findall(r'^\s*theorem\s+([A-Za-z0-9_]+)', data, re.M))
        body = []
        for line in data.splitlines():
            match = re.fullmatch(r'import (\S+)', line)
            if match:
                if match[1] not in modules and match[1] not in imports:
                    imports.append(match[1])
            else:
                body.append(line)
        bodies.append('-- Source: ' + path.name + '\n' + '\n'.join(body))
    need(len(roots) == len(set(roots)) and roots, 'Invalid root inventory')
    return '\n'.join('import ' + m for m in imports) + '\n\n' + '\n\n'.join(bodies) + '\n', roots, hashes


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--dependency-project', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--repository', type=Path, default=HERE.parents[1])
    ap.add_argument('--original-proof-run', type=Path)
    ap.add_argument('--parameter-proof-run', type=Path)
    ap.add_argument('--original-proof-continuation', type=Path,
                    help='Successful all-owned continuation of the completed original source build')
    ap.add_argument('--await-original-proof-continuation', action='store_true',
                    help='Overlap the new independent kernel replay with an already running input continuation; require its complete PASS before recording overall PASS')
    args = ap.parse_args()
    lean = args.lean.resolve(strict=True)
    repo = args.repository.resolve(strict=True)
    need(bool(args.original_proof_run) == bool(args.parameter_proof_run), 'Provide both input runs or neither')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    git = subprocess.check_output([str(lean), '--githash'], text=True).strip()
    need(git == COMMIT and 'version 4.34.1' in version and digest(lean) == COMPILER_SHA256,
         'Wrong pinned official Lean toolchain')
    base = repo / 'formalizations/bapat-q-permanent-dependencies'
    original = repo / 'formalizations/bapat-q-permanent-counterexample'
    package_manifest = json.loads((base / 'lake-manifest.json').read_text())
    libraries, revisions = [], {}
    for p in package_manifest['packages']:
        checkout = args.dependency_project.resolve() / '.lake/packages' / p['name']
        rev = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'], text=True).strip()
        need(rev == p['rev'], 'Wrong package Git revision: ' + p['name'])
        lib = checkout / '.lake/build/lib/lean'
        need(lib.is_dir(), 'Missing official package cache: ' + p['name'])
        libraries.append(lib)
        revisions[p['name']] = rev
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    commands = []

    def shell_command(argv, log, allow_failure=False):
        started = time.monotonic()
        with (output / log).open('wb') as f:
            result = subprocess.run(list(map(str, argv)), stdout=f, stderr=subprocess.STDOUT)
        commands.append({'argv': list(map(str, argv)), 'log': log, 'exit': result.returncode,
                         'seconds': round(time.monotonic() - started, 3)})
        print(log + ': exit=' + str(result.returncode), flush=True)
        need(result.returncode == 0 or allow_failure, 'Failed input proof command; see ' + str(output / log))
        return result.returncode

    continuation = args.original_proof_continuation
    need(continuation is None or args.original_proof_run is not None,
         'Explicit continuation requires the paired existing input source runs')
    if args.original_proof_run:
        original_run = args.original_proof_run.resolve(strict=True)
        parameter_run = args.parameter_proof_run.resolve(strict=True)
        mode = 'Reuse two completed fresh source proof runs; new bridge freshly compiled and its full closure replayed.'
    else:
        parameter_run = output / 'parameter-input'
        shell_command([sys.executable, base / 'replay.py', '--lean', lean,
                       '--dependency-project', args.dependency_project, '--output', parameter_run], 'parameter-input.log')
        restored = output / 'restored-original'
        shell_command([sys.executable, '-B', original / 'scripts/restore_evidence.py',
                       '--output', restored], 'restore-original.log')
        prefix = subprocess.check_output([str(lean), '--print-prefix'], text=True).strip()
        work = output / 'original-input'
        original_rc = shell_command([sys.executable, '-B', restored / 'reproduce.py', '--toolchain', prefix,
                       '--packages-root', args.dependency_project.resolve() / '.lake/packages',
                       '--work-dir', work], 'original-input.log', allow_failure=True)
        runs = list((work / 'verifier/tasks/bapat-n200').iterdir())
        need(len(runs) == 1, 'Ambiguous original input run')
        original_run = runs[0]
        mode = 'Both input proof packages and the new bridge freshly source compiled; all required proof closures replayed.'
        if original_rc != 0:
            continuation = output / 'original-continuation'
            shell_command([sys.executable, '-B', HERE / 'verify_original_input.py', '--lean', lean,
                           '--dependency-project', args.dependency_project, '--proof-run', original_run,
                           '--repository', repo, '--output', continuation], 'continue-original-input.log')
            mode = 'Both input source packages freshly compiled; original full owned proof checked by successful continuation after its reproducer failed. New bridge freshly compiled and fully replayed.'

    original_status = json.loads((original_run / 'manifest/status.json').read_text())
    need(original_status['status'] == 'PASS' or continuation is not None,
         'Original input requires PASS or a separately successful complete continuation')
    original_case = json.loads((original_run / 'manifest/input.json').read_text())
    published_case = json.loads((original / 'evidence/formalization/verify.json').read_text())
    need(original_case['modules'] == published_case['modules'], 'Original module inventory/source hashes changed')
    need(set(original_case['audit_modules']) == set(original_case['modules']), 'Original input audit excluded owned modules')
    original_hashes, input_artifacts = {}, {}
    for name, info in original_case['modules'].items():
        source = original_run / 'sources' / info['path']
        need(digest(source) == info['sha256'], 'Original input source changed: ' + name)
        original_hashes[info['path']] = digest(source)
        artifact = original_run / 'build' / Path(*name.split('.')).with_suffix('.olean')
        input_artifacts['original/' + name + '.olean'] = digest(artifact)
    original_health = json.loads((original_run / 'manifest/environment.json').read_text())
    need(original_health['lean_commit'] == git and original_health['lean_binary_sha256'] == digest(lean),
         'Original input used a different compiler')
    need({p['name']: p['commit'] for p in original_health['packages']} == revisions,
         'Original input package revisions changed')
    def validate_original_completion():
        nonlocal continuation, mode
        continuation_report = None
        if continuation is None:
            original_replay = json.loads((original_run / 'manifest/replay-summary.json').read_text())
        else:
            continuation = continuation.resolve(strict=True)
            continuation_report = json.loads((continuation / 'report.json').read_text())
            need(continuation_report['driver_sha256'] == digest(HERE / 'verify_original_input.py') and
                 continuation_report['status'] == 'PASS', 'Continuation driver/result mismatch')
            for name, h in continuation_report['payload_sha256'].items():
                need(digest(continuation / name) == h, 'Continuation evidence changed: ' + name)
            need(continuation_report['original_source_sha256'] == original_hashes and
                 continuation_report['compiler_sha256'] == digest(lean) and
                 continuation_report['package_revisions'] == revisions and
                 continuation_report['negative_controls_rejected'] == 1,
                 'Continuation source/compiler/pins/negative-control mismatch')
            need(continuation_report['original_case_sha256'] == digest(original_run / 'manifest/input.json') and
                 continuation_report['original_owned_inventory_sha256'] == digest(original_run / 'manifest/owned-inventory.json') and
                 continuation_report['original_source_compile_commands_sha256'] == digest(original_run / 'manifest/commands.json'),
                 'Continuation changed the source build evidence')
            for name, h in continuation_report['original_artifact_sha256'].items():
                need(input_artifacts['original/' + name + '.olean'] == h, 'Continuation artifact changed: ' + name)
            original_replay = continuation_report
            if args.original_proof_run:
                mode = 'Reuse completed fresh 22-module source compilation and successful 928-owned proof continuation after the original reproducer timed out; reuse completed fresh 52-theorem input. New bridge freshly compiled and fully replayed.'
        need(original_replay['status'] == 'PASS' and original_replay['trust_level'] == 0 and
             original_replay['empty_base'] is True and original_replay['owned_count'] == 928 and
             original_replay['all_owned_closure_count'] == 22371,
             'Original input did not replay all owned declarations from an empty kernel')
        return original_replay, continuation_report
    need(not args.await_original_proof_continuation or continuation is not None,
         'Await mode requires a specified original continuation')
    original_pending = (continuation is not None and not (continuation / 'report.json').is_file())
    need(not original_pending or args.await_original_proof_continuation,
         'Original continuation has not completed')
    original_replay, continuation_report = (None, None) if original_pending else validate_original_completion()
    parameter_report = json.loads((parameter_run / 'report.json').read_text())
    published_parameter = json.loads((base / 'verification/report.json').read_text())
    need(parameter_report['status'] == 'PASS' and parameter_report['positive_theorems'] == 52,
         'Parameter input run is not the completed 52-theorem package')
    need(parameter_report['owned_source_sha256'] == published_parameter['owned_source_sha256'],
         'Parameter input source inventory changed')
    for name, h in parameter_report['owned_source_sha256'].items():
        need(digest(base / name) == h, 'Published parameter input source changed: ' + name)
    need(parameter_report['package_revisions'] == revisions and parameter_report['compiler_sha256'] == digest(lean),
         'Parameter input compiler/dependencies changed')
    need((parameter_run / 'ProofBundle.lean').read_bytes() == (base / 'verification/ProofBundle.lean').read_bytes(),
         'Parameter input bundle is not the published frozen bundle')
    for name, h in parameter_report['log_sha256'].items():
        need(digest(parameter_run / name) == h, 'Parameter input log changed: ' + name)
    input_artifacts['parameter/ProofBundle.olean'] = digest(parameter_run / 'ProofBundle.olean')

    bundle, roots, sources = assemble(HERE)
    (output / 'ExplicitBundle.lean').write_text(bundle)
    audit = 'import ExplicitBundle\n' + '\n'.join('#print axioms ' + r for r in roots) + '\n'
    (output / 'AxiomAudit.lean').write_text(audit)
    template = (HERE / 'ReplayTemplate.lean').read_text()
    (output / 'Replay.lean').write_text(template.replace('ROOT_LIST', '[' + ',\n    '.join('``' + r for r in roots) + ']'))
    (output / 'FalseCoordinateBound.lean').write_bytes((HERE / 'FalseCoordinateBound.lean').read_bytes())
    environment = os.environ.copy()
    environment['LEAN_PATH'] = os.pathsep.join(map(str, [output, parameter_run, original_run / 'build'] + libraries))
    report = {'scope': 'Complete original-interval complex Hermitian dimension-200 counterexample with the paper\'s specified rational epsilon/q0, actual ordered data, and rational-complex entries. The separate real-symmetric existence theorem is not certified.',
              'input_mode': mode, 'compiler_version': version, 'compiler_git_commit': git,
              'compiler_sha256': digest(lean), 'package_revisions': revisions,
              'owned_source_sha256': sources, 'roots': roots,
              'original_source_sha256': original_hashes, 'parameter_source_sha256': parameter_report['owned_source_sha256'],
              'imported_owned_artifact_sha256': input_artifacts,
              'original_replay_summary': original_replay,
              'original_saved_status': original_status,
              'original_continuation_report': continuation_report,
              'parameter_empty_kernel_declarations': parameter_report['empty_kernel_declarations'],
              'driver_sha256': digest(HERE / 'replay.py'), 'template_sha256': digest(HERE / 'ReplayTemplate.lean'),
              'module_inventory_sha256': digest(HERE / 'MODULES.json'),
              'original_case_sha256': digest(original / 'evidence/formalization/verify.json'),
              'parameter_report_sha256': digest(base / 'verification/report.json'),
              'generated_source_sha256': {}, 'log_sha256': {}}

    def run(name, extra=()):
        started = time.monotonic()
        r = subprocess.run([str(lean), '-j2', '-M6144', *extra, name], cwd=output,
                           env=environment, capture_output=True)
        data = r.stdout + r.stderr
        log = Path(name).stem + '.log'
        (output / log).write_bytes(data)
        report['generated_source_sha256'][name] = digest(output / name)
        report['log_sha256'][log] = sha256(data).hexdigest()
        commands.append({'source': name, 'exit': r.returncode, 'log': log,
                         'seconds': round(time.monotonic() - started, 3)})
        print(name + ': exit=' + str(r.returncode), flush=True)
        return r.returncode, data.decode(errors='replace')

    rc, text = run('ExplicitBundle.lean', ['-o', 'ExplicitBundle.olean'])
    need(rc == 0 and 'sorry' not in text, 'Fresh explicit source compile failed:\n' + text)
    rc, text = run('AxiomAudit.lean')
    need(rc == 0, 'Axiom audit failed:\n' + text)
    ax = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
    need({n for n, _ in ax} | set(empty) == set(roots), 'Axiom audit excluded an owned theorem')
    for n, a in ax:
        need(set(filter(None, (x.strip() for x in a.split(',')))) <= ALLOWED, 'Unexpected axiom: ' + n)
    rc, text = run('Replay.lean')
    need(rc == 0, 'Empty-kernel replay failed:\n' + text)
    match = re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero', text)
    need(match is not None and int(match[2]) == len(roots), 'Missing full replay PASS')
    rc, text = run('FalseCoordinateBound.lean')
    need(rc != 0 and 'decide' in text.lower() and 'false' in text.lower(),
         'Material false data bound was not rejected:\n' + text)
    if original_pending:
        print('New bridge proof PASS; awaiting complete independent original owned-closure PASS.', flush=True)
        deadline = time.monotonic() + 7200
        while not (continuation / 'report.json').is_file():
            need(time.monotonic() < deadline, 'Original continuation did not complete within two hours')
            time.sleep(15)
        original_replay, continuation_report = validate_original_completion()
    for name, info in original_case['modules'].items():
        artifact = original_run / 'build' / Path(*name.split('.')).with_suffix('.olean')
        need(digest(artifact) == input_artifacts['original/' + name + '.olean'],
             'Original input build artifact changed during bridge replay: ' + name)
    need(digest(parameter_run / 'ProofBundle.olean') == input_artifacts['parameter/ProofBundle.olean'],
         'Parameter input build artifact changed during bridge replay')
    for name, h in sources.items():
        need(digest(HERE / name) == h, 'Owned source changed during bridge replay: ' + name)
    report.update(original_replay_summary=original_replay,
                  original_continuation_report=continuation_report, input_mode=mode)
    sources['FalseCoordinateBound.lean'] = digest(HERE / 'FalseCoordinateBound.lean')
    report.update(status='PASS', positive_theorems=len(roots), empty_kernel_declarations=int(match[1]),
                  negative_controls_rejected=1, allowed_axioms=sorted(ALLOWED), commands=commands)
    (output / 'report.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: report[k] for k in ['status', 'positive_theorems', 'empty_kernel_declarations', 'negative_controls_rejected']}))


if __name__ == '__main__':
    main()
