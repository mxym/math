#!/usr/bin/env python3
"""Check exact source/manuscript hashes. This is an integrity check, not proof verification."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def inventory():
    paths=[]
    for pattern in ('*.py','*.md','*.tex','*.pdf'):
        paths.extend(ROOT.glob(pattern))
    paths.extend(ROOT/p for p in ('.gitattributes','.gitignore'))
    return {p.relative_to(ROOT).as_posix():sha(p) for p in sorted(set(paths))}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',action='store_true');args=ap.parse_args()
    actual=inventory();path=ROOT/'SOURCE_HASHES.json'
    if args.write:
        path.write_text(json.dumps(actual,indent=2)+'\n')
        print('SOURCE_HASHES_WRITTEN',len(actual),'files; no proof verification claimed');return
    expected=json.loads(path.read_text())
    if actual!=expected:raise RuntimeError('Source inventory or digest mismatch')
    binding=json.loads((ROOT/'verification/manuscript-build.json').read_text())
    for family in ('inputs','outputs'):
        for name,h in binding[family].items():
            if sha(ROOT/name)!=h:raise RuntimeError('Manuscript binding mismatch: '+name)
    print('SOURCE_AND_MANUSCRIPT_HASHES_PASS',len(actual),'files; mathematical argument checked separately')

if __name__=='__main__':main()
