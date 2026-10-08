#!/usr/bin/env python3
"""Build a local whitelist-only manuscript archive. No publication or network I/O."""
from pathlib import Path
import argparse, hashlib, json, zipfile
ROOT = Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', default='dimension_structure_candidate.zip')
    args = ap.parse_args()
    wl = json.loads((ROOT/'PUBLIC_WHITELIST.json').read_text())['files']
    assert len(wl) == len(set(wl)), 'duplicate whitelist entries'
    for name in wl:
        p=Path(name)
        assert not p.is_absolute() and '..' not in p.parts, name
        if name != 'SHA256SUMS':
            assert (ROOT/p).is_file() and not (ROOT/p).is_symlink(), name
    hashed = [x for x in wl if x != 'SHA256SUMS']
    (ROOT/'SHA256SUMS').write_text(''.join(f'{sha(ROOT/x)}  {x}\n' for x in sorted(hashed)))
    dest = ROOT/args.output
    with zipfile.ZipFile(dest, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name in sorted(wl):
            info=zipfile.ZipInfo(name, (2026,10,8,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED
            info.external_attr=(0o100755 if name.endswith(('.sh','.py')) else 0o100644)<<16
            z.writestr(info,(ROOT/name).read_bytes())
    print(json.dumps({'archive':str(dest),'files':len(wl),'bytes':dest.stat().st_size,'sha256':sha(dest)},indent=2))
if __name__=='__main__':main()
