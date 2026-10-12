#!/usr/bin/env python3
"""Clean kernel compilation of every delivered mathematical source module.

Run through lake env. Uses a new proof-check directory; never clears an
inherited affine-checkpoint cache. Official mathlib cache may be selected
with ENTRY005_MATHLIB_OVERLAY. No unchecked proof evaluation is used.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
sources = [root / 'Entry005.lean']
for prefix in ['Entry005', 'Mxym', 'OAI']:
    sources += sorted((root / prefix).rglob('*.lean'))
modules = {p.relative_to(root).with_suffix('').as_posix().replace('/', '.'): p for p in sources}
seen, visiting, order = set(), set(), []

def visit(name):
    if name in visiting:
        raise RuntimeError('Cyclic owned import: ' + name)
    if name in seen:
        return
    visiting.add(name)
    for dep in re.findall(r'^import\s+(\S+)', modules[name].read_text(), re.M):
        if dep.startswith(('Entry005.', 'Mxym.', 'OAI.')) or dep == 'Entry005':
            if dep not in modules:
                raise RuntimeError('Missing delivered source: ' + dep)
            visit(dep)
    visiting.remove(name)
    seen.add(name)
    order.append(name)

for module in modules:
    visit(module)
build = root / '.lake/pyramid-proof-check'
if build.is_symlink():
    raise RuntimeError('Refusing a symlinked proof-check directory')
if build.exists():
    shutil.rmtree(build)
lib = build / 'lib/lean'
lib.mkdir(parents=True)
env = os.environ.copy()
overlay = env.get('ENTRY005_MATHLIB_OVERLAY')
env['LEAN_PATH'] = str(lib) + ':' + ((overlay + ':') if overlay else '') + env.get('LEAN_PATH', '')
subprocess.run(['lean', '--version'], cwd=root, env=env, check=True)
for name in order:
    path = modules[name].relative_to(root)
    output = lib / path.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    print('KERNEL_COMPILE ' + name, flush=True)
    subprocess.run(['lean', '-DautoImplicit=false', str(path), '-o', str(output),
                    '-i', str(output.with_suffix('.ilean'))], cwd=root, env=env, check=True)
print(f'CLEAN_PYRAMID_BUILD_PASS {len(order)} modules', flush=True)
