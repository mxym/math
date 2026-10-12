#!/usr/bin/env python3
"""Verify the complete published payload, then run the portable static audit.
Python standard library only. Does not run Lean or change the evidence.
"""
from pathlib import Path
if not __debug__:
    raise SystemExit('Run without Python -O or PYTHONOPTIMIZE: assertions are required.')
import hashlib,json,subprocess,sys
B=Path(__file__).resolve().parent
manifest=json.loads((B/'CURRENT_PUBLIC_MANIFEST.json').read_text())
files={x['path']:x for x in manifest['files']}
assert len(files)==len(manifest['files']), 'Duplicate manifest paths'
actual={str(p.relative_to(B)) for p in B.rglob('*') if p.is_file()}
assert not any(p.is_symlink() for p in B.rglob('*')), 'Symlinks are not part of this snapshot'
assert actual==set(files)|{'CURRENT_PUBLIC_MANIFEST.json','SHA256SUMS'}, {'missing':sorted(set(files)-actual),'extra':sorted(actual-set(files)-{'CURRENT_PUBLIC_MANIFEST.json','SHA256SUMS'})}
for name,row in files.items():
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    data=(B/name).read_bytes()
    assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob_sha1'],name
expected=set(files)|{'CURRENT_PUBLIC_MANIFEST.json'}
seen=set()
for line in (B/'SHA256SUMS').read_text().splitlines():
    h,name=line.split('  ',1)
    assert name not in seen and name in expected,name
    seen.add(name)
    assert hashlib.sha256((B/name).read_bytes()).hexdigest()==h,name
assert seen==expected
print(json.dumps({'all_public_payload_files':'PASS','payload_count':len(files),'checksum_entries':len(seen),'manifest_and_inventory_complete':True},indent=2),flush=True)
subprocess.run([sys.executable,str(B/'audit/audit_record.py')],check=True)
