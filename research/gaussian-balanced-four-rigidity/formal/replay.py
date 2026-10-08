#!/usr/bin/env python3
"""Fresh-source partial Lean replay; no claim about the analytic endpoint."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', type=Path, required=True)
    libs = parser.add_mutually_exclusive_group(required=True)
    libs.add_argument('--dependency-project', type=Path)
    libs.add_argument('--library-root', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    lean = args.lean.resolve()
    version = subprocess.run([str(lean), '--version'], capture_output=True, check=True).stdout.decode()
    need('4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version,
         'Use the pinned official Lean 4.34.1 compiler.')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    if args.library_root:
        paths = [args.library_root.resolve()]
        dependency_mode = 'caller-supplied library cache; entire used proof closure rechecked'
    else:
        project = args.dependency_project.resolve()
        manifest = json.loads((HERE / 'lake-manifest.json').read_text())
        paths = []
        for package in manifest['packages']:
            checkout = project / '.lake/packages' / package['name']
            rev = subprocess.run(['git', '-C', str(checkout), 'rev-parse', 'HEAD'],
                                 capture_output=True, check=True).stdout.decode().strip()
            need(rev == package['rev'], 'Dependency revision mismatch: ' + package['name'])
            library = checkout / '.lake/build/lib/lean'
            need(library.is_dir(), 'Missing official cache: ' + str(library))
            paths.append(library)
        dependency_mode = 'all Lake package revisions checked; used proof closure rechecked'
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [output] + paths))
    for name in ('Algebra.lean', 'Replay.lean', 'FalseBound.lean'):
        shutil.copyfile(HERE / name, output / name)
    report = {'scope': 'rank obstruction, projection, elimination, Taylor margin and local-system algebra only',
              'compiler_version': version.strip(),
              'compiler_sha256': sha256(lean.read_bytes()).hexdigest(),
              'dependencies': dependency_mode, 'sources': {}, 'logs': {}}

    def run(name, extra=()):
        result = subprocess.run([str(lean), *extra, name], cwd=output, env=env,
                                capture_output=True)
        data = result.stdout + result.stderr
        log = Path(name).stem + '.log'
        (output / log).write_bytes(data)
        report['sources'][name] = sha256((output / name).read_bytes()).hexdigest()
        report['logs'][log] = sha256(data).hexdigest()
        return result.returncode, data.decode(errors='replace')

    rc, text = run('Algebra.lean', ('-o', 'Algebra.olean'))
    need(rc == 0, 'Algebra compilation failed:\n' + text)
    need('sorry' not in text, 'Admitted declaration in positive output')
    lines = re.findall(r"'BalancedFour\.([^']+)' depends on axioms: \[([^]]*)\]", text)
    need({name for name, _ in lines} ==
         {'radon_obstruction', 'projection_bound', 'interior_elimination', 'profile_margin', 'linearized_isolation'}, 'Axiom output incomplete')
    for name, axioms in lines:
        need(set(filter(None, (a.strip() for a in axioms.split(',')))) <= ALLOWED,
             'Unexpected axioms: ' + name)
    rc, text = run('Replay.lean')
    need(rc == 0, 'Empty-kernel replay failed:\n' + text)
    match = re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; 5 roots; trust level zero', text)
    need(match is not None, 'Missing replay result')
    report['empty_kernel_declarations'] = int(match[1])
    rc, text = run('FalseBound.lean')
    need(rc != 0 and 'unsolved goals' in text, 'False bound was not rejected as expected:\n' + text)
    report.update(status='PASS', positive_theorems=5, negative_controls_rejected=1,
                  allowed_axioms=sorted(ALLOWED), analytic_endpoint_formalized=False)
    (output / 'report.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: report[k] for k in ('status', 'scope', 'positive_theorems',
          'empty_kernel_declarations', 'negative_controls_rejected')}, indent=2))


if __name__ == '__main__':
    main()
