#!/usr/bin/env python3
"""Continue a finished 22-module source build with one full owned-closure replay.

This does not overwrite the original timed-out run status or pretend its driver
finished. It audits/replays all owned declarations in one union, avoiding the
original runner's repeated individual closure traversals.
"""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import time

from replay import ALLOWED, COMMIT, COMPILER_SHA256

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--dependency-project', type=Path, required=True)
    p.add_argument('--proof-run', type=Path, required=True)
    p.add_argument('--repository', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    lean, run = a.lean.resolve(strict=True), a.proof_run.resolve(strict=True)
    need(digest(lean) == COMPILER_SHA256 and
         subprocess.check_output([str(lean), '--githash'], text=True).strip() == COMMIT,
         'Wrong compiler')
    original = a.repository / 'formalizations/bapat-q-permanent-counterexample'
    base = a.repository / 'formalizations/bapat-q-permanent-dependencies'
    case = json.loads((run / 'manifest/input.json').read_text())
    published = json.loads((original / 'evidence/formalization/verify.json').read_text())
    need(case['modules'] == published['modules'] and len(case['modules']) == 22,
         'Source inventory changed')
    commands = json.loads((run / 'manifest/commands.json').read_text())
    for name, info in case['modules'].items():
        src = run / 'sources' / info['path']
        need(digest(src) == info['sha256'], 'Source changed: ' + name)
        matches = [c for c in commands if '-o' in c['argv'] and str(src) in c['argv']]
        need(len(matches) == 1 and matches[0]['exit_code'] == 0, 'No completed source compile: ' + name)
    inventory = json.loads((run / 'manifest/owned-inventory.json').read_text())
    roots = [v['declaration']['name'] for v in inventory]
    need(len(roots) == len(set(roots)) == 928 and
         json.loads((run / 'manifest/violations.json').read_text()) == [], 'Original owned audit failed')
    for value in inventory:
        need(set(value['axioms']) <= ALLOWED, 'Unallowed original owned axiom')
    health = json.loads((run / 'manifest/environment.json').read_text())
    need(health['lean_commit'] == COMMIT and health['lean_binary_sha256'] == digest(lean),
         'Source build compiler changed')
    libs, revisions = [], {}
    for entry in json.loads((base / 'lake-manifest.json').read_text())['packages']:
        checkout = a.dependency_project / '.lake/packages' / entry['name']
        rev = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'], text=True).strip()
        need(rev == entry['rev'], 'Package revision changed')
        revisions[entry['name']] = rev
        libs.append(checkout / '.lake/build/lib/lean')
    need(revisions == {v['name']: v['commit'] for v in health['packages']}, 'Source build package pins changed')
    artifacts = {name: digest(run / 'build' / Path(*name.split('.')).with_suffix('.olean'))
                 for name in case['modules']}
    output = a.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    template = (HERE / 'ReplayTemplate.lean').read_text().replace('import ExplicitBundle',
        '\n'.join('import ' + name for name in case['module_order']))
    template = template.replace('        | _ => []',
        '        | .defnInfo v => v.all\n        | .thmInfo v => v.all\n'
        '        | .opaqueInfo v => v.all\n        | .quotInfo _ => [``Eq]\n        | _ => []')
    def lean_name(name):
        value = 'Name.anonymous'
        for part in name.split('.'):
            value = ('(Name.num ' + value + ' ' + part + ')') if part.isdecimal() else (
                '(Name.str ' + value + ' ' + json.dumps(part, ensure_ascii=False) + ')')
        return value

    source = template.replace('ROOT_LIST', '[' + ',\n    '.join(lean_name(n) for n in roots) + ']')
    module_strings = '[' + ', '.join(json.dumps(n) for n in case['module_order']) + ']'
    source = source.replace('  let cs ← match collect env roots {} with',
        '  let modules : List String := ' + module_strings + '\n'
        '  let owned := env.constants.fold (init := #[]) fun acc n _ =>\n'
        '    match env.getModuleIdxFor? n with\n'
        '    | none => acc\n'
        '    | some i => if modules.contains env.header.moduleNames[i.toNat]!.toString\n'
        '                then acc.push n else acc\n'
        '  unless owned.size == roots.length && owned.all (fun n => roots.contains n) do\n'
        '    throwError "Owned declaration inventory differs from actual imported sources"\n'
        '  let cs ← match collect env roots {} with')
    (output / 'ReplayOriginal.lean').write_text(source)
    (output / 'FalseKernel.lean').write_text('import BapatN200Matrix\nexample : False := by decide +kernel\n')
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [output, run / 'build', *libs]))
    results = []
    for name in ['ReplayOriginal.lean', 'FalseKernel.lean']:
        start = time.monotonic()
        result = subprocess.run([str(lean), '-j2', '-M6144', name], cwd=output, env=env, capture_output=True)
        data = result.stdout + result.stderr
        (output / name.replace('.lean', '.log')).write_bytes(data)
        results.append({'source': name, 'exit': result.returncode,
                        'seconds': round(time.monotonic() - start, 3)})
        text = data.decode(errors='replace')
        print(name, result.returncode, flush=True)
        if name == 'ReplayOriginal.lean':
            match = re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero', text)
            need(result.returncode == 0 and match is not None and
                 (int(match[1]), int(match[2])) == (22371, 928), 'Full original replay failed:\n' + text)
        else:
            need(result.returncode != 0 and 'false' in text.lower(), 'False control was not rejected')
    for name, h in artifacts.items():
        need(digest(run / 'build' / Path(*name.split('.')).with_suffix('.olean')) == h,
             'Input artifact changed during replay')
    report = {'status': 'PASS', 'scope': 'Continuation of completed fresh 22-source compilation and full 928-owned-declaration audit; one complete empty-kernel closure replay and false control. Original driver timed out and is not relabelled PASS.',
              'owned_count': 928, 'all_owned_closure_count': 22371, 'trust_level': 0, 'empty_base': True,
              'compiler_commit': COMMIT, 'compiler_sha256': digest(lean), 'package_revisions': revisions,
              'original_source_sha256': {v['path']: v['sha256'] for v in case['modules'].values()},
              'original_artifact_sha256': artifacts, 'original_case_sha256': digest(run / 'manifest/input.json'),
              'original_owned_inventory_sha256': digest(run / 'manifest/owned-inventory.json'),
              'original_source_compile_commands_sha256': digest(run / 'manifest/commands.json'),
              'driver_sha256': digest(HERE / 'verify_original_input.py'),
              'negative_controls_rejected': 1, 'commands': results,
              'payload_sha256': {q.name: digest(q) for q in output.iterdir() if q.is_file()}}
    (output / 'report.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print('ORIGINAL_FULL_OWNED_CONTINUATION_PASS', flush=True)


if __name__ == '__main__':
    main()
