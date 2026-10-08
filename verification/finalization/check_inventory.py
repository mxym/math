#!/usr/bin/env python3
"""Check the published manuscript bytes; this does not prove the mathematics."""
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import sys
import argparse
import subprocess

ROOT=Path(__file__).resolve().parents[2]
MANIFEST=ROOT/'manuscripts/MANIFEST.json'


def need(ok,message):
    if not ok:raise RuntimeError(message)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--tracked',action='store_true',
                        help='Also check Git staging includes every published byte')
    args=parser.parse_args()
    data=json.loads(MANIFEST.read_text())
    need(data['schema']=='integrated-research-manuscripts-v1','wrong inventory schema')
    expected=data['files']
    actual=set()
    for prefix in ('manuscripts','verification/finalization'):
        for p in (ROOT/prefix).rglob('*'):
            if '__pycache__' in p.parts:continue
            need(not p.is_symlink(),'symlink in manuscript payload: '+str(p))
            if p.is_file() and p!=MANIFEST:actual.add(str(p.relative_to(ROOT)))
    need(actual==set(expected),'inventory differs: '+str(sorted(actual^set(expected))))
    if args.tracked:
        p=subprocess.run(['git','ls-files','-z','--','manuscripts','verification/finalization'],
                         cwd=ROOT,capture_output=True,check=True)
        tracked=set(p.stdout.decode().split('\0'))
        needed=set(expected)|{'manuscripts/MANIFEST.json'}
        need(needed<=tracked,'Git omits publication files: '+str(sorted(needed-tracked)))
    for relative,row in expected.items():
        name=PurePosixPath(relative)
        need(not name.is_absolute() and '..' not in name.parts,'unsafe inventory path')
        p=ROOT/relative;b=p.read_bytes()
        need(len(b)==row['bytes'] and sha256(b).hexdigest()==row['sha256'],
             'published byte mismatch: '+relative)
    print('PASS '+str(len(expected))+' published manuscript/verification files')
    print('Scope: source/PDF/certificate integrity; not a proof or priority certification')


if __name__=='__main__':
    try:main()
    except Exception as e:
        print('FAIL '+str(e),file=sys.stderr)
        raise SystemExit(1)
