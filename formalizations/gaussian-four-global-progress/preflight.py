#!/usr/bin/env python3
"""Fail-closed source inventory checks; this is not a substitute for Lean."""
from __future__ import annotations
import json
from pathlib import Path
import re
from typing import Callable


def check_inventory(root: Path, strip_comments: Callable[[str], str]) -> dict:
    modules = json.loads((root / 'MODULES.json').read_text())
    source_paths = [str((root / p).resolve()) for p in modules.values()]
    if len(source_paths) != len(set(source_paths)):
        raise RuntimeError('Duplicate owned source paths in MODULES.json')
    local_files = {p.resolve() for pattern in ('GaussianFour.lean', 'GaussianFour/**/*.lean', 'analytic/**/*.lean')
                   for p in root.glob(pattern)}
    mapped_files = {Path(p) for p in source_paths}
    missing = local_files - mapped_files
    if missing:
        raise RuntimeError(f'Unlisted owned Lean sources: {sorted(map(str, missing))}')
    seen: set[str] = set()
    edges = []
    for module, relative in modules.items():
        source = root / relative
        if not source.is_file():
            raise RuntimeError(f'Missing source for {module}: {relative}')
        code = strip_comments(source.read_text())
        for line in code.splitlines():
            match = re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+)$', line)
            if not match:
                continue
            for dependency in match.group(1).split():
                if dependency == 'Mathlib':
                    raise RuntimeError(f'Unbounded Mathlib umbrella import in {module}')
                if dependency.split('.')[0] in {'Mathlib', 'Lean', 'Std', 'Batteries', 'Aesop', 'Qq'}:
                    continue
                if dependency not in modules:
                    raise RuntimeError(f'Unlisted owned import {dependency} in {module}')
                if dependency not in seen:
                    raise RuntimeError(f'Build order puts {module} before {dependency}')
                edges.append([dependency, module])
        seen.add(module)
    roots = (root / 'ROOTS.txt').read_text().splitlines()
    if not roots or len(roots) != len(set(roots)):
        raise RuntimeError('Empty or duplicate audit roots')
    audited = re.findall(r'^#print axioms (\S+)$', (root / 'audit/Audit.lean').read_text(), re.M)
    replay = (root / 'audit/Replay.lean').read_text().split('  let roots := [', 1)[1].split('  let cs', 1)[0]
    replayed = re.findall(r'``([A-Za-z0-9_.]+)', replay)
    if roots != audited or roots != replayed:
        raise RuntimeError('ROOTS.txt, Audit.lean, and Replay.lean disagree')
    return {'status': 'PASS', 'modules': len(modules), 'roots': len(roots), 'owned_import_edges': edges}


if __name__ == '__main__':
    from reproduce import ROOT, strip_comments, source_snapshot
    source_snapshot()
    result = check_inventory(ROOT, strip_comments)
    print(json.dumps({k: v for k, v in result.items() if k != 'owned_import_edges'}, sort_keys=True))
