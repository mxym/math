#!/usr/bin/env python3
"""Check pinned public sources in explicit local checkouts; no network or writes."""
import argparse,hashlib,json,pathlib,sys
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--upstream-root',required=True,type=pathlib.Path,help='Root of openai/math checkout or extracted tree')
p.add_argument('--mxym-root',required=True,type=pathlib.Path,help='Root of mxym/math checkout or extracted tree')
a=p.parse_args();roots={'upstream':a.upstream_root.resolve(),'mxym':a.mxym_root.resolve()}
here=pathlib.Path(__file__).resolve().parent
m=json.loads((here/'dependency-inventory.json').read_text());fail=[]
for r in m['files']:
    rel=pathlib.PurePosixPath(r['path'])
    if rel.is_absolute() or '..' in rel.parts:fail.append('Unsafe path '+r['path']);continue
    target=roots[r['repository']].joinpath(*rel.parts)
    if not target.is_file():fail.append('Missing '+r['repository']+':'+r['path']);continue
    d=target.read_bytes()
    sha=hashlib.sha256(d).hexdigest();blob=hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
    if len(d)!=r['bytes'] or sha!=r['sha256'] or blob!=r['git_blob_sha1']:
        fail.append('Changed '+r['repository']+':'+r['path']);continue
    for label in r.get('source_labels',[]):
        if '\\label{'+label+'}' not in d.decode():fail.append('Missing label '+label+' in '+r['path'])
if fail:print('\n'.join(fail),file=sys.stderr);sys.exit(1)
print(f"PASS: all {len(m['files'])} public dependency files match pinned lengths, SHA-256, Git blob hashes, and labels.")
for n,r in m['repositories'].items():print(n+': '+r['url']+' at '+r['commit'])
