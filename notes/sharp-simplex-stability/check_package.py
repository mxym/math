#!/usr/bin/env python3
"""Read-only package integrity, exact whitelist and source pins; checks remain under -O."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import sys
import zipfile
ROOT = Path(__file__).resolve().parent
EXCLUDE={'MANIFEST.json','SHA256SUMS','source.zip'}

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def digest(path):
    return len(path.read_bytes()),hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    require(sys.argv[1:] in ([],['--extracted']),'Only --extracted is supported')
    extracted=bool(sys.argv[1:])
    names=(ROOT/'PACKAGE_FILES.txt').read_text().splitlines()
    require(names == sorted(set(names)),'Whitelist must be sorted and unique')
    for name in names:
        p=PurePosixPath(name)
        require(name and not p.is_absolute() and '..' not in p.parts and str(p)==name,'Unsafe whitelist path')
    actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and p.relative_to(ROOT).parts[0] not in {'build','__pycache__'}}
    require(actual == set(names)-({'source.zip'} if extracted and not (ROOT/'source.zip').exists() else set()),'Whitelist mismatch: '+repr(sorted(actual^set(names))))
    for name in actual:
        require(not (ROOT/name).is_symlink(),'Symlink payload: '+name)
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    require(manifest['excluded_to_avoid_self_reference']==sorted(EXCLUDE),'Unexpected exclusions')
    entries={f['path']:f for f in manifest['files']}
    require(len(entries)==len(manifest['files']) and set(entries)==set(names)-EXCLUDE,'Manifest coverage mismatch')
    for name,f in entries.items():
        require(digest(ROOT/name)==(f['bytes'],f['sha256']),'Hash/size mismatch: '+name)
    require((ROOT/'SHA256SUMS').read_text()==''.join(entries[name]['sha256']+'  '+name+'\n' for name in names if name not in EXCLUDE),'SHA256SUMS mismatch')
    sources=json.loads((ROOT/'PROVENANCE.json').read_text())['source_files']
    for f in sources:
        require(digest(ROOT/f['path'])==(f['bytes'],f['sha256']),'Pinned source mismatch: '+f['path'])
    if (ROOT/'source.zip').exists():
        with zipfile.ZipFile(ROOT/'source.zip') as z:
            members=['sharp-simplex-stability/'+name for name in names if name!='source.zip']
            require(z.namelist()==members,'Archive whitelist/order mismatch')
            require(z.testzip() is None,'Archive CRC failure')
            for name in names:
                if name!='source.zip':
                    require(z.read('sharp-simplex-stability/'+name)==(ROOT/name).read_bytes(),'Archive byte mismatch: '+name)
    else:
        require(extracted,'Archive missing')
    print('Package integrity PASS: '+str(len(entries))+' payload hashes, '+str(len(sources))+' pinned sources, exact whitelist.')

if __name__=='__main__':
    main()
