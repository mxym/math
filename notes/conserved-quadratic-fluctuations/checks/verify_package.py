#!/usr/bin/env python3
"""Verify whitelist, exact inventory, safe paths and every listed content hash."""
from __future__ import annotations
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent

def require(ok,message):
    if not ok: raise RuntimeError(message)

def safe(name):
    p=Path(name)
    require(isinstance(name,str) and bool(name) and not p.is_absolute() and '..' not in p.parts and p.as_posix()==name,'Unsafe or noncanonical path: '+str(name))
    return p

def inventory():
    actual=set()
    for p in ROOT.rglob('*'):
        require(not p.is_symlink(),'Symlink is not a public file: '+str(p.relative_to(ROOT)))
        if not p.is_file(): continue
        rel=p.relative_to(ROOT)
        if '__pycache__' in rel.parts or rel.suffix=='.pyc': continue
        actual.add(rel.as_posix())
    return actual

def main():
    whitelist=json.loads((ROOT/'PUBLIC_FILES.json').read_text()); allowed=whitelist['files']
    require(len(allowed)==len(set(allowed)),'Duplicate whitelist path.')
    for name in allowed: safe(name)
    require('package-manifest.json' not in allowed,'Manifest must be self-excluded.')
    manifest=json.loads((ROOT/'package-manifest.json').read_text()); rows=manifest['files']; names=[row['path'] for row in rows]
    require(len(names)==len(set(names)),'Duplicate manifest path.')
    require(set(names)==set(allowed),'Manifest does not match publication whitelist.')
    require(inventory()==set(allowed)|{'package-manifest.json'},'Unexpected or missing public files: '+str(sorted(inventory()^(set(allowed)|{'package-manifest.json'}))))
    for row in rows:
        p=ROOT/safe(row['path']);data=p.read_bytes()
        require(len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'],'Content mismatch: '+row['path'])
    print(json.dumps({'verified_files':len(rows),'exact_inventory':True,'whitelist_match':True,'all_hashes_match':True},indent=2))
if __name__=='__main__':
    try: main()
    except (OSError,ValueError,RuntimeError,KeyError) as e: raise SystemExit('PACKAGE CHECK FAILED: '+str(e))
