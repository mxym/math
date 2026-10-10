#!/usr/bin/env python3
"""Explicit maintainer operation; review the diff and commit updated pins.
Never called by reproduce.py or CI. No source or dependency is altered.
"""
from pathlib import Path
import hashlib
import json
ROOT=Path(__file__).resolve().parent
registry=json.loads((ROOT/'MODULES.json').read_text())
paths=[f'../gaussian-measure-primal-dual/{m}.lean' for m in registry['base']]
paths += [f'{m}.lean' for m in registry['proof']+registry['entry']+registry['target_statements']]
paths += ['lakefile.lean','lake-manifest.json','lean-toolchain','DEPENDENCY_PINS.json',
          'TOOLCHAIN_PINS.json','MODULES.json','ROOTS.json','SCOPE.json','reproduce.py',
          'fetch_cache.sh','update_source_manifest.py','proof-dependencies.dot']
paths += [str(p.relative_to(ROOT)) for p in (ROOT/'audit').iterdir() if p.suffix in {'.lean','.json'}]
result={}
for relative in sorted(set(paths)):
    data=(ROOT/relative).read_bytes().replace(b'\r\n',b'\n')
    result[relative]=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
(ROOT/'SOURCE_BLOBS.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(f'{len(result)} source/config/checker files pinned; review and commit before verification')
