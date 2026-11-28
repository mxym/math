#!/usr/bin/env python3
"""Replay refined continuous bounds using the byte-pinned predecessor oracle."""
import hashlib,importlib.util,sys
from pathlib import Path

OLD = Path(__file__).with_name('verify-kissing-nine-gram-cells.py')
if hashlib.sha256(OLD.read_bytes()).hexdigest() != 'f18bcd13cb34be3e5dce6d2d5dcb7449c410368e91c2ded9c6ebe2d17de8b5cb':
    raise SystemExit('unexpected predecessor; use the version identified in the article')
spec = importlib.util.spec_from_file_location('kissing_gram_oracle', OLD)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
if sys.argv[1:] == ['census']:
    mod.census(7,3); mod.census(9,4); raise SystemExit
if len(sys.argv) not in (2,3) or sys.argv[1] not in ('5','7','9'):
    raise SystemExit('usage: verifier.py census | 5|7|9 [class]')
n = int(sys.argv[1]); idx = {5:0,7:1,9:2}[n]
target = {5:252000,7:202000,9:163000}[n]
graphs = mod.GRAPHS[idx]
if n==5:
    G=graphs[0]
    assert len(graphs)==1 and all(x.bit_count()==2 for x in G)
    assert all(not ((G[a]>>b)&1 and G[a]&G[b]) for a in range(5) for b in range(a))
ids=range(len(graphs)) if len(sys.argv)==2 else [int(sys.argv[2])]
for j in ids:
    if not 0<=j<len(graphs):raise ValueError('class out of range')
    print('BEGIN',n,j,flush=True)
    if not mod.solve(graphs[j],target,120000):raise RuntimeError('unclosed continuous cell')
    print('PASS',n,j,flush=True)
