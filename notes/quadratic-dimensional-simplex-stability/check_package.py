#!/usr/bin/env python3
"""Strict integrity and derivative checks. No check depends on Python assert."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import zipfile
from make_package import FILES,ROOT,archive_bytes

# These trusted publication-copy fingerprints bind the three proof files.
EXPECTED_PROOFS={'QUADRATIC_DIMENSION_THEOREM.md': '3db48eeb9424bae7678253d803420b43908b93611231767353977a939db14423', 'INTRINSIC_NORM_CONVERSION.md': '3f527129e3c799d39eda14dd8a9f5714fd9b84bf5cef94d52acb4716d2406cf6', 'intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md': '680cba26ca1bdc47605f8366d3fe5a1c495716c138d3c1a85bbd377e84484448'}
EXPECTED_BASIS='e4692f094731baa994ae10a2d81bc0b50334ed65bb5e5f676c3e48d5b21fe978'


def sha(data):return hashlib.sha256(data).hexdigest()


def need(ok,message):
    if not ok:raise RuntimeError(message)


def read(name):
    path=ROOT/name
    need(path.is_file() and not path.is_symlink(),'Missing file or symlink: '+name)
    return path.read_bytes()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--extracted',action='store_true')
    args=parser.parse_args()
    need(len(FILES)==len(set(FILES)) and FILES==sorted(FILES),'Invalid fixed payload enumeration')
    allowed=set(FILES+['MANIFEST.json','SHA256SUMS','source.zip','results/verification.json'])
    for path in ROOT.rglob('*'):
        rel=path.relative_to(ROOT).as_posix()
        need(not path.is_symlink(),'Symlink prohibited: '+rel)
        if path.is_file():
            cache=bool(re.fullmatch(r'__pycache__/make_package\.cpython-[0-9]+(?:\.opt-[0-9]+)?\.pyc',rel))
            need(rel in allowed or cache,'Unlisted file: '+rel)
    manifest=json.loads(read('MANIFEST.json'))
    rows=manifest['files']
    need([r['path'] for r in rows]==FILES,'Manifest enumeration differs from fixed payload')
    for row in rows:
        b=read(row['path'])
        need(len(b)==row['bytes'] and sha(b)==row['sha256'],'Manifest mismatch: '+row['path'])
    expected_sums=''.join(sha(read(name))+'  '+name+'\n' for name in sorted(FILES+['MANIFEST.json']))
    need(read('SHA256SUMS').decode()==expected_sums,'Checksum list is incomplete, duplicated, reordered, or mismatched')
    for name,digest in EXPECTED_PROOFS.items():need(sha(read(name))==digest,'Frozen public proof differs: '+name)
    fidelity=json.loads(read('SOURCE_FIDELITY.json'))
    need(fidelity['basis_archive_sha256']==EXPECTED_BASIS,'Wrong frozen basis')
    for row in fidelity['unchanged_files']:
        data=read(row['path'])
        need(len(data)==row['bytes'] and sha(data)==row['sha256'],'Unchanged source mismatch: '+row['path'])
    ledger=json.loads(read('SANITIZATION_LEDGER.json'))
    need(ledger['basis_archive_sha256']==EXPECTED_BASIS,'Wrong ledger basis')
    for row in ledger['derivatives']:
        data=read(row['path']);lines=data.decode().splitlines(keepends=True)
        need(sha(data)==row['after_sha256'] and len(data)==row['after_bytes'],'Derivative mismatch: '+row['path'])
        expected_line=1
        for part in row['segments']:
            start=part['public_start_line'];end=part['public_end_line']
            need(start==expected_line and end>=start-1,'Noncontiguous source-fidelity segments')
            frag=''.join(lines[start-1:end]).encode()
            need(sha(frag)==part['public_sha256'],'Public segment differs')
            if part['kind']=='equal':need(part['original_sha256']==part['public_sha256'],'Unchanged segment not source-identical')
            expected_line=end+1
        need(expected_line==len(lines)+1,'Incomplete source-fidelity segment coverage')
        for edit in row['edits']:need(sha(edit['replacement'].encode())==edit['after_fragment_sha256'],'Replacement record differs')
    for row in json.loads(read('SOURCE_PINS.json'))['sources']:
        data=read(row['path'])
        need(len(data)==row['bytes'] and sha(data)==row['sha256'],'Source pin mismatch: '+row['path'])
        if 'url' in row:need(bool(re.fullmatch(r'https://github\.com/mxym/math/blob/[0-9a-f]{40}/.+',row['url'])),'Source URL lacks exact commit')
    for row in json.loads(read('AUDITED_ORIGINAL_SOURCE_HASHES.json'))['sources']:
        data=read(row['public_path'])
        need(len(data)==row['public_bytes'] and sha(data)==row['public_sha256'],'Original/public mapping differs')
        if row['byte_identical']:need(row['original_sha256']==row['public_sha256'],'False identity claim')
    for row in json.loads(read('sources/HISTORICAL_SOURCE_PINS.json'))['sources']:
        data=read(row['path'])
        need(len(data)==row['bytes'] and sha(data)==row['sha256'],'Historical exact import differs')
    # Scan all published text, including exact copies. The checker itself names
    # forbidden patterns as data and is exempt from this one test only.
    for name in FILES:
        text=read(name).decode()
        if name!='check_package.py':
            for pattern in ['/workspace/','/home/agent/','/root/','research_math/','sediment://','codex://']:
                need(pattern not in text,'Private locator in '+name)
        # Exact historical source copies retain original repository-context links.
        if name.endswith('.md') and not name.startswith('sources/'):
            for target in re.findall(r'\]\(([^)]+)\)',text):
                if target.startswith(('https://','http://','#')):continue
                if not any(c in target for c in ('.','/','#')):continue  # Mathematical [factor](S-z) is not a file link.
                path=(ROOT/name).parent/target.split('#')[0]
                need(path.is_file(),'Broken release link in '+name+': '+target)
    arc=ROOT/'source.zip'
    if arc.exists():
        need(arc.read_bytes()==archive_bytes(),'Archive differs from deterministic payload')
        with zipfile.ZipFile(arc) as z:
            need(z.namelist()==sorted(FILES+['MANIFEST.json','SHA256SUMS']),'Archive enumeration mismatch')
            need(z.testzip() is None,'Archive CRC failure')
    else:need(args.extracted,'Archive missing; use --extracted for an extracted source archive')
    print('PASS: '+str(len(FILES))+' fixed payload files, source fidelity, pins, public links, strict checksums'+(', deterministic archive.' if arc.exists() else '.'))

if __name__=='__main__':main()
