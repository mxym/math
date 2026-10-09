#!/usr/bin/env python3
"""Pin all proof, data, generator, build, control and replay sources."""
import argparse,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent

def build_manifest():
    paths=set((ROOT/'APPT').rglob('*.lean'))
    paths.update((ROOT/'Verification').rglob('*.lean'))
    paths.update(ROOT.glob('*.lean'))
    paths.update(ROOT.glob('*.py'))
    paths.update((ROOT/'scripts').rglob('*.py'))
    paths.update((ROOT/'scripts/templates').glob('*.txt'))
    paths.update((ROOT/'certificates').glob('*.json'))
    paths.update(ROOT.glob('generated-*.json'))
    for name in ['lakefile.toml','lake-manifest.json','lean-toolchain','NECESSITY_SOURCES.json']:
        paths.add(ROOT/name)
    return {p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    data=build_manifest();path=ROOT/'PROOF_SOURCES.json'
    if args.check:
        if json.loads(path.read_text())!=data:raise RuntimeError('Manifest does not cover the exact current proof package')
        print('COMPLETE_SOURCE_MANIFEST_PASS',len(data),'files')
    else:
        path.write_text(json.dumps(data,indent=2)+'\n')
        print('COMPLETE_SOURCE_MANIFEST_WRITTEN',len(data),'files')
