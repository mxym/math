#!/usr/bin/env python3
"""Reproduce the delivered kernel build and verify exact source / axiom coverage."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'formal'
LOGS = ROOT / 'logs'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def uncomment(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s[i:i + 2] == '/-':
            depth += 1
            i += 2
        elif depth and s[i:i + 2] == '-/':
            depth -= 1
            i += 2
        elif not depth and s[i:i + 2] == '--':
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        else:
            out.append(s[i] if not depth or s[i] == '\n' else ' ')
            i += 1
    require(depth == 0, 'Unclosed Lean comment')
    return ''.join(out)

def axiom_items(text):
    require(not re.search(r'\b(error|warning)\s*:', text), 'Compiler diagnostics in successful evidence')
    items = [(a or c, {x.strip() for x in b.split(',') if x.strip()}) for a, b, c in
        re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]|'([^']+)' does not depend on any axioms", text)]
    require(len(items) == len({a for a, _ in items}), 'Duplicate axiom report')
    require(all(axioms <= ALLOWED for _, axioms in items), 'Nonstandard or hidden axiom in proof closure')
    return dict(items)

def check_sources():
    sources = []
    for table in ['frozen-147-source-hashes.json', 'new-pyramid-source-hashes.json',
                  'owner-unchanged-source-hashes.json']:
        for record in json.loads((ROOT / 'sources' / table).read_text()):
            p = ROOT / record['path']
            require(hashlib.sha256(p.read_bytes()).hexdigest() == record['sha256'],
                    'Changed verified source: ' + record['path'])
            sources.append(p)
    require(len(sources) == 101 and len(set(sources)) == 101, 'Incorrect delivered module set')
    for p in sources:
        code = uncomment(p.read_text())
        require(not re.search(r'\b(sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|extern)\b|debug\.skipKernelTC', code),
                'Forbidden proof escape in ' + str(p))
    require(hashlib.sha256((FORMAL / 'Entry005/Targets.lean').read_bytes()).hexdigest() ==
            '8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94', 'Canonical research definitions changed')
    return sources

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--skip-build', action='store_true', help='Reuse this directory\'s already successful clean source build')
    args = parser.parse_args()
    LOGS.mkdir(exist_ok=True)
    env = os.environ.copy()
    if args.lean_bin:
        env['PATH'] = str(args.lean_bin.resolve()) + ':' + env.get('PATH', '')
    check_sources()
    path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=FORMAL, env=env, text=True).strip()
    proofenv = env.copy()
    overlay = env.get('ENTRY005_MATHLIB_OVERLAY')
    proofenv['LEAN_PATH'] = str(FORMAL / '.lake/pyramid-proof-check/lib/lean') + ':' + ((overlay + ':') if overlay else '') + path
    def run(argv, log, runenv=env):
        result = subprocess.run(argv, cwd=FORMAL, env=runenv, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (LOGS / log).write_text(result.stdout)
        require(result.returncode == 0, 'Failed ' + log)
        require(not re.search(r'\b(error|warning)\s*:', result.stdout), 'Diagnostics in ' + log)
        print('PASS ' + log, flush=True)
        return result.stdout
    run(['python3', 'scripts/check_pins.py'], 'pyramid-pins.log')
    run(['python3', '-O', 'scripts/check_pins.py'], 'pyramid-pins-optimized.log')
    if not args.skip_build:
        run(['lake', 'env', 'python3', 'scripts/clean_pyramid_build.py'], 'pyramid-clean-build-release.log')
    build = (LOGS / 'pyramid-clean-build-release.log').read_text()
    require('CLEAN_PYRAMID_BUILD_PASS 102 modules' in build, 'No full clean build evidence')
    require(not re.search(r'\b(error|warning)\s*:', build), 'Clean build contains diagnostics')
    jobs = [('PyramidAllStatements', 'pyramid-clean-714-statements.log'),
            ('PyramidFinalAudit', 'pyramid-clean-82-statements.log'),
            ('PyramidOwnedDeclarations', 'pyramid-clean-owned-declarations.log'),
            ('PyramidOwnedClosure', 'pyramid-clean-owned-closure.log'),
            ('PyramidPublicDeclarations', 'pyramid-clean-public-declarations.log')]
    with ThreadPoolExecutor(max_workers=3) as pool:
        results = list(pool.map(lambda j: run(['lean', '-DautoImplicit=false', j[0] + '.lean'], j[1], proofenv), jobs))
    report = axiom_items(results[0])
    expected = json.loads((ROOT / 'sources/all-public-theorems.json').read_text())
    require(set(report) == set(expected) and len(report) == 714, 'Public signature/axiom inventory mismatch')
    new = axiom_items(results[1])
    require(set(new) == set(json.loads((ROOT / 'sources/pyramid-all-public-theorems.json').read_text())) and len(new) == 82,
            'New proof signature/axiom inventory mismatch')
    owned = re.findall(r'^OWNED_DECL (.+)$', results[2], re.M)
    closure = axiom_items(results[3])
    require(set(owned) == set(closure) and len(owned) == len(closure), 'Incomplete module-owned closure audit')
    # Match every source theorem to its actual declaring module in the environment.
    public = {name: module for module, name in re.findall(r'^PUBLIC_THEOREM (\S+) (\S+)$', results[4], re.M)}
    require(set(expected) <= set(public), 'An expected theorem is absent from the actual environment')
    bymodule = json.loads((ROOT / 'sources/all-public-theorems-by-module.json').read_text())
    for source, names in bymodule.items():
        module = Path(source).relative_to('formal').with_suffix('').as_posix().replace('/', '.')
        require(all(public[name] == module for name in names), 'Wrong actual declaring module for ' + source)
    for p in sorted((FORMAL / 'controls').glob('*.lean')):
        run(['lean', '-DautoImplicit=false', str(p.relative_to(FORMAL))], 'pyramid-control-' + p.stem + '.log', proofenv)
    verification = {'clean_mathematical_module_count': 102, 'public_source_theorem_count': 714,
        'new_public_theorem_count': 82, 'unchanged_affine_checkpoint_theorem_count': 147,
        'module_owned_declaration_count': len(owned), 'allowed_axioms': sorted(ALLOWED),
        'new_axioms_by_theorem': {k: sorted(v) for k, v in new.items()},
        'all_axioms_by_theorem': {k: sorted(v) for k, v in report.items()},
        'all_module_owned_axioms': {k: sorted(v) for k, v in closure.items()},
        'actual_finite_pyramid_and_B_proved': True, 'actual_common_limit_entryA_and_D_proved': True,
        'same_polar_law_and_assignment_witness_preserved': True,
        'full_main_proved': False, 'sharpness_proved': False, 'warnings': 0}
    (LOGS / 'pyramid-verification.json').write_text(json.dumps(verification, indent=2) + '\n')
    print('PYRAMID_VERIFICATION_PASS 102 modules, 714 public proofs, 82 new exports', flush=True)

if __name__ == '__main__':
    main()
