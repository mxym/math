#!/usr/bin/env python3
"""Create a deterministic source archive from an explicit checked whitelist."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import zipfile
ROOT = Path(__file__).resolve().parent
EXCLUDE={'MANIFEST.json','SHA256SUMS','source.zip'}

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def main():
    names=(ROOT/'PACKAGE_FILES.txt').read_text().splitlines()
    require(names == sorted(set(names)), 'Whitelist must be sorted and unique')
    for name in names:
        p=PurePosixPath(name)
        require(name and not p.is_absolute() and '..' not in p.parts and str(p)==name,'Unsafe archive path')
        if name not in EXCLUDE:
            require((ROOT/name).is_file() and not (ROOT/name).is_symlink(),'Missing/unsafe payload: '+name)
    actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and p.relative_to(ROOT).parts[0] not in {'build','__pycache__'}}
    require(actual-EXCLUDE == set(names)-EXCLUDE,'Whitelist does not match files')
    entries=[{'path':name,'bytes':(ROOT/name).stat().st_size,'sha256':hashlib.sha256((ROOT/name).read_bytes()).hexdigest()} for name in names if name not in EXCLUDE]
    (ROOT/'MANIFEST.json').write_text(json.dumps({'schema':'sharp-simplex-stability-package-v1','excluded_to_avoid_self_reference':sorted(EXCLUDE),'files':entries},indent=2)+'\n')
    (ROOT/'SHA256SUMS').write_text(''.join(e['sha256']+'  '+e['path']+'\n' for e in entries))
    with zipfile.ZipFile(ROOT/'source.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for name in names:
            if name=='source.zip':
                continue
            info=zipfile.ZipInfo('sharp-simplex-stability/'+name,(2026,10,7,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED
            info.external_attr=0o100644<<16
            z.writestr(info,(ROOT/name).read_bytes())
    print('Created deterministic source-complete archive with '+str(len(names)-1)+' members.')

if __name__=='__main__':
    main()
