#!/usr/bin/env python3
"""Mandatory pin checks use explicit failures, including under Python -O."""
from pathlib import Path
import json
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parent.parent
LEAN = 'leanprover/lean4:v4.34.1'
COMPILER = '5045d0056413266e57c625dcd7c365b10e377c52'
EXPECTED = {
    'mathlib': ('https://github.com/leanprover-community/mathlib4.git', 'd13f23b723b8a846827a245b89c10fc7d3f11612'),
    'plausible': ('https://github.com/leanprover-community/plausible', '118aa17ee84656b8bd727fef7c458ee8c833385c'),
    'LeanSearchClient': ('https://github.com/leanprover-community/LeanSearchClient', 'ddf04cf3949fa556442341e87d47f9f6e6074707'),
    'importGraph': ('https://github.com/leanprover-community/import-graph', 'e928b72544873815af278d38681b31c0293588e3'),
    'proofwidgets': ('https://github.com/leanprover-community/ProofWidgets4', '106ff4fafc74ef4ac99d81dbf3ab399118f497a5'),
    'aesop': ('https://github.com/leanprover-community/aesop', '355695d523e41d0554926416cba2a2b3544fbbc9'),
    'Qq': ('https://github.com/leanprover-community/quote4', '6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259'),
    'batteries': ('https://github.com/leanprover-community/batteries', 'f2effa3d803fda822b1f97b806c47cf2adfbcbc2'),
    'Cli': ('https://github.com/leanprover/lean4-cli', 'e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204'),
}

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

require((ROOT / 'lean-toolchain').read_text().strip() == LEAN, 'Lean toolchain pin mismatch')
config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
require(config.get('fixedToolchain') is True, 'fixedToolchain must be true in project configuration')
requirements = [r for r in config.get('require', []) if r.get('name') == 'mathlib']
require(len(requirements) == 1, 'Expected exactly one mathlib requirement')
require(requirements[0].get('rev') == EXPECTED['mathlib'][1], 'mathlib source pin mismatch')
require(requirements[0].get('git') == EXPECTED['mathlib'][0], 'mathlib source URL mismatch')
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
require(manifest.get('fixedToolchain') is True, 'fixedToolchain must be true in lockfile')
packages = manifest.get('packages', [])
names = [p.get('name') for p in packages]
require(len(names) == len(set(names)) and set(names) == set(EXPECTED), 'Dependency package set mismatch')
for package in packages:
    name = package['name']
    require(package.get('rev') == EXPECTED[name][1], f'Locked revision mismatch for {name}')
    require(package.get('url') == EXPECTED[name][0], f'Locked source URL mismatch for {name}')
version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
require('version 4.34.1,' in version and COMPILER in version, 'Installed compiler version/commit mismatch')
print(version)
print(subprocess.check_output(['lake', '--version'], cwd=ROOT, text=True).strip())
for package in packages:
    name = package['name']
    checkout = ROOT / manifest['packagesDir'] / name
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
    require(head == package['rev'], f'Checkout revision mismatch for {name}: {head}')
    dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                    cwd=checkout, text=True).strip()
    require(not dirty, f'Tracked dependency sources modified: {name}')
    print(f'{name}: {head} (tracked sources clean)')
print('PASS: compiler and all nine dependency pins match; checks remain active under Python -O.')
