#!/usr/bin/env python3
"""Fresh Lean compilation, pinned-dependency audit and trust-zero kernel replay."""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

LEAN_COMMIT = '5045d0056413266e57c625dcd7c365b10e377c52'
MODULES = ['FourRowBasic', 'FourRowLaplace', 'FourRowInequality', 'FourRowSharpness', 'FourRowNorm', 'FourRowTradeoff', 'PairRigidity', 'CriticalProducts', 'MatrixRigidity', 'ExtremizerValues', 'EqualityClassification', 'FourRowCompleteEquality']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)

def capture(cmd: list[str], cwd: Path, env: dict[str, str]) -> str:
    p = subprocess.run(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True, check=False)
    require(p.returncode == 0, f'Command failed: {cmd}\n{p.stdout}')
    return p.stdout.strip()

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dependency-project', type=Path)
    ap.add_argument('--lean', type=Path)
    ap.add_argument('--work-dir', type=Path)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    dep = (args.dependency_project or root).resolve()
    manifest = json.loads((root / 'PROOF_SOURCES.json').read_text())
    def verify_sources() -> None:
        for name, digest in manifest['files'].items():
            require(sha(root / name) == digest, f'Source hash mismatch: {name}')
    verify_sources()
    for module in MODULES:
        text = (root / f'{module}.lean').read_text()
        require(re.search(r'\b(sorry|admit|axiom|native_decide)\b', text) is None,
                f'Forbidden proof token in {module}')
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    if args.lean:
        env['PATH'] = str(args.lean.resolve().parent) + os.pathsep + env.get('PATH', '')
    lean = shutil.which('lean', path=env.get('PATH'))
    lake = shutil.which('lake', path=env.get('PATH'))
    require(lean is not None and lake is not None, 'Lean and Lake must be available')
    version = capture([lean, '--version'], dep, env)
    require('version 4.34.1,' in version and LEAN_COMMIT in version,
            f'Unexpected Lean version: {version}')
    prefix = Path(capture([lean, '--print-prefix'], dep, env))
    actual_lean = prefix / 'bin' / 'lean'
    require(actual_lean.is_file(), f'Cannot resolve actual Lean executable: {actual_lean}')
    pins = json.loads((root / 'lake-manifest.json').read_text())
    actual_pins = {}
    for package in pins['packages']:
        require(package['type'] == 'git' and len(package['rev']) == 40,
                f'Unpinned dependency: {package["name"]}')
        package_path = dep / '.lake' / 'packages' / package['name']
        actual = capture(['git', '-C', str(package_path), 'rev-parse', 'HEAD'], dep, env)
        require(actual == package['rev'], f'Dependency mismatch: {package["name"]}')
        dirty = capture(['git', '-C', str(package_path), 'status', '--porcelain', '--untracked-files=no'], dep, env)
        require(not dirty, f'Tracked dependency sources modified: {package["name"]}')
        actual_pins[package['name']] = actual
    if args.work_dir:
        work = args.work_dir.resolve()
        require(not work.exists(), 'The fresh work directory must not already exist')
        work.mkdir(parents=True)
    else:
        work = Path(tempfile.mkdtemp(prefix='four-row-fresh-'))
    for name in manifest['files']:
        if name.endswith('.lean') or name in {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}:
            shutil.copy2(root / name, work / name)
    (work / '.lake' / 'build' / 'lib' / 'lean').mkdir(parents=True)
    (work / '.lake' / 'packages').symlink_to((dep / '.lake' / 'packages').resolve(), target_is_directory=True)
    require(not list(work.rglob('*.olean')), 'Fresh directory unexpectedly contains compiled objects')
    started = dt.datetime.now(dt.timezone.utc).isoformat()
    commands = []
    def run_logged(command: list[str], logfile: str) -> str:
        p = subprocess.run(command, cwd=work, env=env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, check=False)
        (work / logfile).write_text(p.stdout)
        commands.append({'command': command, 'log': logfile, 'returncode': p.returncode})
        print(logfile, 'exit', p.returncode, flush=True)
        require(p.returncode == 0, f'Verification command failed. See {work / logfile}\n{p.stdout}')
        require('sorryAx' not in p.stdout, f'Unexpected sorry axiom in {logfile}')
        return p.stdout
    for module in MODULES:
        run_logged([lake, 'env', 'lean', '-o', f'.lake/build/lib/lean/{module}.olean',
                    f'{module}.lean'], f'build-{module}.log')
    run_logged([lake, 'env', 'lean', 'PositiveControls.lean'], 'positive-controls.log')
    run_logged([lake, 'env', 'lean', 'Statements.lean'], 'main-statements.log')
    out = run_logged([lake, 'env', 'lean', 'Replay.lean'], 'empty-kernel-replay.log')
    match = re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero', out)
    require(match is not None, 'Missing successful trust-zero replay result')
    actual_axioms = set((work / 'replayed-axioms.txt').read_text().splitlines())
    require(actual_axioms <= ALLOWED_AXIOMS, f'Unexpected axioms: {actual_axioms}')
    roots = (work / 'replayed-roots.txt').read_text().splitlines()
    require(sorted(roots) == sorted(manifest['roots']), 'Replayed root list differs from manifest')
    require(len(roots) == int(match.group(2)), 'Replay root count mismatch')
    closure = (work / 'replayed-closure.txt').read_text().splitlines()
    require(len(closure) == int(match.group(1)), 'Replay closure count mismatch')
    negative_controls = []
    for name in ['RejectMissingNonzero', 'RejectWrongWeight']:
        command = [lake, 'env', 'lean', f'{name}.lean']
        p = subprocess.run(command, cwd=work, env=env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, check=False)
        logfile = f'{name}.log'
        (work / logfile).write_text(p.stdout)
        require(p.returncode != 0 and 'unsolved goals' in p.stdout,
                f'Negative control did not fail at the proof goal: {name}\n{p.stdout}')
        negative_controls.append({'name': name, 'returncode': p.returncode,
                                  'log': logfile, 'sha256': sha(work / logfile)})
        print(name, 'EXPECTED_REJECTION', flush=True)
    verify_sources()
    for module in MODULES:
        require(sha(work / f'{module}.lean') == manifest['files'][f'{module}.lean'],
                f'Fresh source changed during verification: {module}')
    result = {'status': 'FRESH_COMPILE_AND_EMPTY_KERNEL_REPLAY_PASS',
              'started_utc': started, 'completed_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
              'work_directory': str(work), 'lean_version': version,
              'actual_lean_sha256': sha(actual_lean), 'dependencies': actual_pins,
              'module_count': len(MODULES), 'root_count': len(roots),
              'closure_count': len(closure), 'trust_level': 0,
              'axioms': sorted(actual_axioms), 'source_hashes': manifest['files'],
              'olean_sha256': {m: sha(work / '.lake/build/lib/lean' / f'{m}.olean') for m in MODULES},
              'commands': commands, 'negative_controls': negative_controls,
              'positive_control_count': 3,
              'log_sha256': {c['log']: sha(work / c['log']) for c in commands}}
    (work / 'VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'module_count', 'root_count',
                     'closure_count', 'trust_level', 'axioms', 'work_directory']}, indent=2), flush=True)

if __name__ == '__main__':
    main()
