#!/usr/bin/env python3
"""Compile frozen owned source in a fresh bundle; replay every theorem in an empty kernel."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--dependency-project', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    lean = args.lean.resolve()
    version = subprocess.run([str(lean), '--version'], capture_output=True, check=True).stdout.decode().strip()
    need('4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version,
         'Use official Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52.')
    manifest = json.loads((HERE / 'lake-manifest.json').read_text())
    paths = []
    revisions = {}
    for package in manifest['packages']:
        checkout = args.dependency_project.resolve() / '.lake/packages' / package['name']
        revision = subprocess.run(['git', '-C', str(checkout), 'rev-parse', 'HEAD'],
                                  capture_output=True, check=True).stdout.decode().strip()
        need(revision == package['rev'], 'Dependency revision mismatch: ' + package['name'])
        path = checkout / '.lake/build/lib/lean'
        need(path.is_dir(), 'Missing official dependency cache: ' + str(path))
        paths.append(path)
        revisions[package['name']] = revision
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    module_specs = json.loads((HERE / 'MODULES.json').read_text())
    modules = [entry['module'] for entry in module_specs]
    namespaces = {entry['module']: entry['namespace'] for entry in module_specs}
    need(len(modules) == len(set(modules)), 'Duplicate module.')
    imports, bodies, roots, sources = [], [], [], {}
    for module in modules:
        source = HERE / (module + '.lean')
        data = source.read_text()
        sources[source.name] = digest(source)
        need(not re.search(r'^\s*(?:axiom|unsafe|partial)\b', data, flags=re.M),
             'Unexpected proof-source declaration: ' + source.name)
        need(not re.search(r'\bsorry\b|\bnative_decide\b', data), 'Admission or native oracle in ' + source.name)
        body = []
        for line in data.splitlines():
            match = re.fullmatch(r'import (\S+)', line)
            if match:
                if match[1] not in modules and match[1] not in imports:
                    imports.append(match[1])
            else:
                body.append(line)
        bodies.append('-- Source: ' + source.name + '\n' + '\n'.join(body))
        roots.extend(namespaces[module] + '.' + name for name in
                     re.findall(r'^\s*theorem\s+([A-Za-z0-9_]+)', data, flags=re.M))
    need(len(roots) == len(set(roots)) and len(roots) > 0, 'Invalid theorem inventory.')
    bundle = '\n'.join('import ' + name for name in imports) + '\n\n' + '\n\n'.join(bodies) + '\n'
    (output / 'ProofBundle.lean').write_text(bundle)
    (output / 'AxiomAudit.lean').write_text('import ProofBundle\n' +
        '\n'.join('#print axioms ' + name for name in roots) + '\n')
    replay = (HERE / 'ReplayTemplate.lean').read_text().replace('ROOT_LIST',
        '[' + ',\n    '.join('``' + name for name in roots) + ']')
    (output / 'Replay.lean').write_text(replay)
    negative = (HERE / 'FalseInterval.lean').read_text().replace('import Controls', 'import ProofBundle')
    (output / 'FalseInterval.lean').write_text(negative)
    sources['FalseInterval.lean'] = digest(HERE / 'FalseInterval.lean')
    report = {
        'scope': 'Actual q-permanent endpoint deleted-minor identity, Hermitian real-value correspondence and positive-definite perturbation/explicit-interval chain. This verifies dependencies only: no full Gram/Bargmann bridge, order-200 integer certificate or asymptotic real counterexample is certified.',
        'compiler_version': version, 'compiler_sha256': digest(lean),
        'package_revisions': revisions, 'owned_source_sha256': sources,
        'roots': roots, 'generated_source_sha256': {}, 'log_sha256': {},
        'source_compile_mode': 'Fresh concatenation of frozen positive modules, with only owned imports removed and external imports deduplicated; no owned olean input.',
        'replay_driver_sha256': digest(HERE / 'replay.py'),
        'replay_template_sha256': digest(HERE / 'ReplayTemplate.lean'),
    }
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [output] + paths))

    def run(name, extra=()):
        started = time.monotonic()
        result = subprocess.run([str(lean), *extra, name], cwd=output, env=env, capture_output=True)
        data = result.stdout + result.stderr
        log = Path(name).stem + '.log'
        (output / log).write_bytes(data)
        report['generated_source_sha256'][name] = digest(output / name)
        report['log_sha256'][log] = sha256(data).hexdigest()
        print(f'{name}: exit={result.returncode}, seconds={time.monotonic()-started:.1f}', flush=True)
        return result.returncode, data.decode(errors='replace')

    rc, text = run('ProofBundle.lean', ('-o', 'ProofBundle.olean'))
    need(rc == 0, 'Fresh source compilation failed:\n' + text)
    need('sorry' not in text, 'Admitted declaration in positive compilation output.')
    rc, text = run('AxiomAudit.lean')
    need(rc == 0, 'Axiom audit failed:\n' + text)
    records = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
    # Lean prints a distinct line for the empty-axiom case.
    empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
    need({name for name, _ in records} | set(empty) == set(roots), 'Incomplete axiom audit.')
    for name, axioms in records:
        need(set(filter(None, (a.strip() for a in axioms.split(',')))) <= ALLOWED,
             'Unexpected axioms in ' + name)
    rc, text = run('Replay.lean')
    need(rc == 0, 'Empty-kernel replay failed:\n' + text)
    match = re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero', text)
    need(match is not None and int(match[2]) == len(roots), 'Missing or incomplete kernel result.')
    rc, text = run('FalseInterval.lean')
    need(rc != 0 and 'unsolved goals' in text and 'False' in text,
         'Omitted-derivative negative control was not rejected as expected:\n' + text)
    report.update(status='PASS', positive_theorems=len(roots),
                  empty_kernel_declarations=int(match[1]), negative_controls_rejected=1,
                  positive_controls=3, allowed_axioms=sorted(ALLOWED))
    (output / 'report.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: report[key] for key in ('status', 'positive_theorems',
          'empty_kernel_declarations', 'positive_controls', 'negative_controls_rejected')}, indent=2))


if __name__ == '__main__':
    main()
