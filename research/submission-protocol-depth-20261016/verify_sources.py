#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
base=Path(__file__).resolve().parent
repo=base.parent.parent
manifest=json.loads((base/'SOURCE_HASHES.json').read_text())
checked=0
for field,anchor in [('files',base),('inherited_repository_inputs',repo)]:
    for rel,want in manifest[field].items():
        path=(anchor/rel).resolve()
        if not path.is_relative_to(anchor):
            raise RuntimeError('path escapes declared base: '+rel)
        got=hashlib.sha256(path.read_bytes()).hexdigest()
        if got!=want:
            raise RuntimeError('source hash mismatch: '+rel+'; expected '+want+' got '+got)
        checked+=1
print(json.dumps({'status':'PASS','bound_files_and_inherited_inputs':checked,'manifest_sha256':hashlib.sha256((base/'SOURCE_HASHES.json').read_bytes()).hexdigest()},indent=2))
