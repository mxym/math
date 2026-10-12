#!/usr/bin/env python3
"""Clean source build and kernel axiom/ownership verification for truncation.

The manifest is frozen before delivery. Every inherited and new mathematical
module is rebuilt into an empty owned output directory. Diagnostic evaluation
enumerates the actual Lean environment and never replaces a proof term.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess

from verify_pyramid import uncomment, axiom_items

ROOT = Path(__file__).resolve().parents[1]
F = ROOT / 'formal'
LOGS = ROOT / 'logs'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def checked_sources():
    paths = []
    for name in ['frozen-147-source-hashes.json', 'new-pyramid-source-hashes.json',
                 'owner-unchanged-source-hashes.json', 'truncation-source-hashes.json']:
        for record in json.loads((ROOT / 'sources' / name).read_text()):
            p = ROOT / record['path']
            require(hashlib.sha256(p.read_bytes()).hexdigest() == record['sha256'],
                    'Changed verified mathematical source: ' + record['path'])
            code = uncomment(p.read_text())
            require(not re.search(r'\b(sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|extern)\b|debug\.skipKernelTC', code),
                    'Forbidden proof escape: ' + record['path'])
            paths.append(p)
    require(len(paths) == len(set(paths)), 'Duplicate mathematical source')
    require(hashlib.sha256((F / 'Entry005/Targets.lean').read_bytes()).hexdigest() ==
        '8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94',
        'Literal research Targets changed')
    paths.append(F / 'Entry005.lean')
    return paths

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    LOGS.mkdir(exist_ok=True)
    env = os.environ.copy()
    if args.lean_bin:
        env['PATH'] = str(args.lean_bin.resolve()) + ':' + env.get('PATH', '')
    sources = checked_sources()
    modules = {p.relative_to(F).with_suffix('').as_posix().replace('/', '.'): p for p in sources}
    visiting, seen, order = set(), set(), []
    def visit(module):
        if module in seen:
            return
        require(module not in visiting, 'Owned import cycle: ' + module)
        visiting.add(module)
        for dep in re.findall(r'^import\s+(\S+)', modules[module].read_text(), re.M):
            if dep == 'Entry005' or dep.startswith(('Entry005.', 'Mxym.', 'OAI.')):
                require(dep in modules, 'Missing delivered mathematical source: ' + dep)
                visit(dep)
        visiting.remove(module)
        seen.add(module)
        order.append(module)
    for module in modules:
        visit(module)
    def run(argv, log, runenv=env):
        result = subprocess.run(argv, cwd=F, env=runenv, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (LOGS / log).write_text(result.stdout)
        require(result.returncode == 0, 'Failed command: ' + log)
        require(not re.search(r'\b(error|warning)\s*:', result.stdout), 'Diagnostics: ' + log)
        print('PASS ' + log, flush=True)
        return result.stdout
    run(['python3', 'scripts/check_pins.py'], 'truncation-pins.log')
    run(['python3', '-O', 'scripts/check_pins.py'], 'truncation-pins-optimized.log')
    lakepath = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=F, env=env, text=True).strip()
    clean = F / '.lake/truncation-proof-check'
    if not args.skip_build:
        require(not clean.is_symlink(), 'Refusing symlinked clean output directory')
        if clean.exists():
            shutil.rmtree(clean)
        (clean / 'lib/lean').mkdir(parents=True)
    proofenv = env.copy()
    proofenv['LEAN_PATH'] = ':'.join([str(clean / 'lib/lean'),
        *([env['ENTRY005_MATHLIB_OVERLAY']] if env.get('ENTRY005_MATHLIB_OVERLAY') else []), lakepath])
    if not args.skip_build:
        buildlog = [subprocess.check_output(['lean', '--version'], env=env, text=True)]
        for module in order:
            source = modules[module].relative_to(F)
            output = clean / 'lib/lean' / source.with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            result = subprocess.run(['lean', '-DautoImplicit=false', str(source), '-o', str(output),
                '-i', str(output.with_suffix('.ilean'))], cwd=F, env=proofenv,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            buildlog.append('KERNEL_COMPILE ' + module + '\n' + result.stdout)
            (LOGS / 'truncation-clean-build.log').write_text(''.join(buildlog))
            require(result.returncode == 0, 'Failed source module: ' + module)
            require(not re.search(r'\b(error|warning)\s*:', result.stdout), 'Source diagnostics: ' + module)
            print('KERNEL_COMPILE ' + module, flush=True)
        buildlog.append(f'CLEAN_TRUNCATION_BUILD_PASS {len(order)} modules\n')
        (LOGS / 'truncation-clean-build.log').write_text(''.join(buildlog))
    require(f'CLEAN_TRUNCATION_BUILD_PASS {len(order)} modules' in
        (LOGS / 'truncation-clean-build.log').read_text(), 'Missing full clean build evidence')
    jobs = [('audit/truncation-all-statements.lean', 'truncation-all-statements-axioms.log'),
            ('audit/truncation-owned.lean', 'truncation-owned-closure.log')]
    with ThreadPoolExecutor(max_workers=2) as pool:
        statements, closuretext = list(pool.map(lambda job: run(['lean', '-DautoImplicit=false', job[0]],
            job[1], proofenv), jobs))
    exports = axiom_items(statements)
    expected = json.loads((ROOT / 'sources/truncation-public-theorems.json').read_text())
    inherited = json.loads((ROOT / 'sources/all-public-theorems.json').read_text())
    require(set(exports) == set(expected) | set(inherited), 'Export signature/axiom inventory mismatch')
    owned = re.findall(r'^OWNED_DECL (.+)$', closuretext, re.M)
    closures = [(name, {x.strip() for x in axioms.split(',') if x.strip()}) for name, axioms in
        re.findall(r'^OWNED_AXIOMS (.+):\s*\[([^\]]*)\]', closuretext, re.M)]
    require(len(owned) == len(set(owned)) and len(closures) == len(dict(closures)), 'Duplicate owned audit')
    require(set(owned) == set(dict(closures)), 'Incomplete private/generated closure audit')
    require(all(axioms <= ALLOWED for _, axioms in closures), 'Unallowed module-owned axiom')
    public = {name: module for module, name in
        re.findall(r'^PUBLIC_THEOREM (\S+) (\S+)$', closuretext, re.M)}
    require(set(exports) <= set(public), 'Public theorem absent from environment')
    bymodule = json.loads((ROOT / 'sources/truncation-public-by-module.json').read_text())
    bymodule.update(json.loads((ROOT / 'sources/all-public-theorems-by-module.json').read_text()))
    for source, names in bymodule.items():
        module = Path(source).relative_to('formal').with_suffix('').as_posix().replace('/', '.')
        require(all(public[name] == module for name in names), 'Wrong theorem declaring module: ' + source)
    claims = json.loads((ROOT / 'sources/truncation-final-claims.json').read_text())
    report = {'clean_mathematical_module_count': len(order), 'new_public_theorems': len(expected),
        'unchanged_inherited_public_theorems': len(inherited), 'all_public_theorems': len(exports),
        'module_owned_declarations': len(owned), 'allowed_axioms': sorted(ALLOWED), 'warnings': 0,
        'axioms_by_new_theorem': {name: sorted(exports[name]) for name in expected},
        'all_module_owned_axioms': {name: sorted(axioms) for name, axioms in closures}, **claims}
    (LOGS / 'truncation-verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'TRUNCATION_VERIFICATION_PASS {len(order)} modules; {len(expected)} new exports; '+
          f'{len(exports)} combined public proofs; {len(owned)} owned declarations', flush=True)

if __name__ == '__main__':
    main()
