#!/usr/bin/env python3
"""Decode the full recorded graphs outside this public snapshot (no Lean needed)."""
from pathlib import Path
import argparse,base64,gzip,hashlib,json
B=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',type=Path,required=True,help='New nonexistent directory outside this evidence snapshot')
a=ap.parse_args(); W=a.output.resolve()
if W.exists() or W==B or B in W.parents:ap.error('Output must be a new directory outside the public snapshot')
rows=[r for r in json.loads((B/'PUBLICATION_MAPPING.json').read_text())['source_files'] if r['operation']=='lossless gzip base64 parts']
outputs=[]
for row in rows:
    assert row['parts']==sorted(set(row['parts']))
    encoded=b''.join((B/p).read_bytes() for p in row['parts'])
    assert len(encoded)==row['encoded_bytes'] and hashlib.sha256(encoded).hexdigest()==row['encoded_sha256']
    data=gzip.decompress(base64.b64decode(encoded,validate=True))
    assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
    name=row['source_path']; assert not Path(name).is_absolute() and '..' not in Path(name).parts
    outputs.append((name,data))
W.mkdir(parents=True)
for name,data in outputs:
    p=W/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    print(hashlib.sha256(data).hexdigest()+'  '+str(p))
