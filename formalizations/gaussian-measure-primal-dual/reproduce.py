"""Fresh compilation and empty-kernel replay, using read-only pinned dependencies.

First prepare dependencies with `lake update; lake exe cache get`. Alternatively
pass --dependency-project pointing to an already prepared pinned Lake project.
No precompiled artifact of this package is read or distributed.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
from integrity import check

HERE = Path(__file__).resolve().parent
EXPECTED_LEAN_COMMIT = '5045d0056413266e57c625dcd7c365b10e377c52'
MODULES = [
    'GaussianPartition', 'GaussianPrices', 'GaussianNoTies',
    'GaussianFullSupport', 'GaussianBalancedPrices', 'GaussianWinningPartition',
    'GaussianUniquePrices', 'GaussianPrimalDual', 'GaussianFractionalEquality',
]

def fail(message):
    raise RuntimeError(message)

def preflight(lean, dependency_project):
    """Check actual files, Git pins, and toolchain, without compiling or replaying."""
    check(HERE)
    if not lean:
        fail('Lean was not found. Install the toolchain in lean-toolchain or pass --lean.')
    package_dir = dependency_project.resolve() / '.lake' / 'packages'
    pins = json.loads((HERE / 'DEPENDENCY_PINS.json').read_text())
    paths = []
    for name, expected in pins.items():
        package = package_dir / name
        if not package.is_dir():
            fail('Missing dependency ' + name + ': run lake update and lake exe cache get first.')
        actual = subprocess.check_output(['git', '-C', str(package), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != expected:
            fail('Wrong Git pin for ' + name + ': ' + actual)
        artifact_dir = package / '.lake' / 'build' / 'lib' / 'lean'
        if not artifact_dir.is_dir():
            fail('Missing compiled dependency cache for ' + name)
        paths.append(str(artifact_dir))
    version = subprocess.check_output([lean, '--version'], cwd=HERE, text=True).strip()
    if not re.search(r'version 4\.34\.1(?:,|\s)', version):
        fail('Wrong Lean version: ' + version)
    lean_commit = subprocess.check_output([lean, '--githash'], cwd=HERE, text=True).strip()
    if lean_commit != EXPECTED_LEAN_COMMIT:
        fail('Wrong Lean Git commit: ' + lean_commit)
    prefix = Path(subprocess.check_output([lean, '--print-prefix'], cwd=HERE, text=True).strip())
    toolchain_binary = prefix / 'bin' / ('lean.exe' if os.name == 'nt' else 'lean')
    if not toolchain_binary.is_file():
        fail('Cannot identify the actual toolchain Lean binary for hashing.')
    report = {'lean_version': version, 'lean_git_commit': lean_commit,
              'lean_binary_path': str(toolchain_binary),
              'lean_binary_sha256': hashlib.sha256(toolchain_binary.read_bytes()).hexdigest(),
              'package_pins': pins,
              'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'source_sha256': {m + '.lean': hashlib.sha256((HERE / (m + '.lean')).read_bytes()).hexdigest()
                                for m in MODULES + ['Replay']}}
    return report, paths

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dependency-project', type=Path, default=HERE)
    parser.add_argument('--lean', default=shutil.which('lean'))
    parser.add_argument('--work-dir', type=Path)
    parser.add_argument('--preflight-only', action='store_true',
                        help='Verify files, dependency pins, and actual toolchain; do not run Lean proofs.')
    args = parser.parse_args()
    report, paths = preflight(args.lean, args.dependency_project)
    if args.preflight_only:
        if args.work_dir:
            fail('--work-dir is not used with --preflight-only.')
        report['scope'] = 'Preflight only; no source compilation or kernel replay.'
        print('PREFLIGHT_PASS', flush=True)
        print(json.dumps(report, indent=2))
        return
    if args.work_dir:
        work = args.work_dir.resolve()
        if work.exists():
            fail('--work-dir must not exist: the build must start without own artifacts.')
        work.mkdir(parents=True)
    else:
        work = Path(tempfile.mkdtemp(prefix='gaussian-measure-primal-dual-'))
    for name in MODULES + ['Replay']:
        shutil.copyfile(HERE / (name + '.lean'), work / (name + '.lean'))
    shutil.copyfile(HERE / 'lean-toolchain', work / 'lean-toolchain')
    environment = os.environ.copy()
    environment['LEAN_PATH'] = os.pathsep.join([str(work)] + paths)
    for module in MODULES + ['Replay']:
        print('Checking ' + module, flush=True)
        command = [args.lean, '--root=' + str(work)]
        if module != 'Replay':
            command += ['-o', str(work / (module + '.olean'))]
        command += [str(work / (module + '.lean'))]
        with (work / (module + '.log')).open('w') as log:
            result = subprocess.run(command, cwd=work, env=environment,
                                    stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            fail('Lean failed in ' + module + '; see ' + str(work / (module + '.log')))
        print('PASS ' + module, flush=True)
    expected = 'EMPTY_KERNEL_REPLAY_PASS 52742 declarations; 50 roots; trust level zero'
    if expected not in (work / 'Replay.log').read_text():
        fail('The expected successful replay record is missing.')
    closure = (work / 'replayed-closure.txt').read_text().splitlines()
    if len(closure) != 52742 or len(set(closure)) != 52742:
        fail('Incorrect verified closure size or duplicate constant names.')
    axioms = (work / 'replayed-axioms.txt').read_text().splitlines()
    if set(axioms) != {'propext', 'Classical.choice', 'Quot.sound'}:
        fail('Unexpected axiom set: ' + repr(axioms))
    for name in ['replayed-closure.txt', 'replayed-axioms.txt']:
        original = (HERE / 'evidence' / name).read_bytes()
        if (work / name).read_bytes() != original:
            fail('Replayed evidence differs from the frozen record: ' + name)
    report.update({'root_count': 50,
              'closure_count': 52742, 'kernel_trust_level': 0, 'axioms': axioms,
              'source_sha256': {m + '.lean': hashlib.sha256((work / (m + '.lean')).read_bytes()).hexdigest()
                                for m in MODULES + ['Replay']}})
    (work / 'REPRODUCTION.json').write_text(json.dumps(report, indent=2) + '\n')
    print('REPRODUCTION_PASS; evidence at ' + str(work), flush=True)

if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError, subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
