#!/usr/bin/env python3
"""Integrity checks use explicit exceptions and remain active under python -O."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import zipfile
from make_package import FILES, ROOT, archive_bytes

EXPECTED_MAIN = '2b398cba3afd73819dbf90d5106e64be64ba06a07f9e42d23f4c2037ff5cd791'
EXPECTED_CORE = '94c4e777b0000e5e33e024d59c47e258594fbfacc554e4faa91f8b5264c503f5'


def sha(data): return hashlib.sha256(data).hexdigest()

def need(condition, message):
    if not condition: raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--extracted', action='store_true', help='The archive itself is absent after extraction.')
    args = parser.parse_args()
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    rows = manifest['files']
    need([r['path'] for r in rows] == FILES, 'Manifest file list differs from the fixed payload.')
    for r in rows:
        path = ROOT/r['path']
        need(path.is_file() and not path.is_symlink(), 'Missing file or symlink: '+r['path'])
        data = path.read_bytes()
        need(len(data)==r['bytes'] and sha(data)==r['sha256'], 'Manifest mismatch: '+r['path'])
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        h, name = line.split('  ', 1)
        need(name in FILES+['MANIFEST.json'], 'Unexpected checksum member: '+name)
        need(sha((ROOT/name).read_bytes())==h, 'Checksum mismatch: '+name)
    need(len((ROOT/'SHA256SUMS').read_text().splitlines())==len(FILES)+1, 'Incomplete checksum list')
    main_data = (ROOT/'POLYNOMIAL_REFINEMENT.md').read_bytes()
    need(sha(main_data)==EXPECTED_MAIN, 'Frozen mathematical Markdown changed')
    core = b'## 1.' + main_data.split(b'## 1.',1)[1].split(b'## 9.',1)[0]
    need(sha(core)==EXPECTED_CORE, 'Frozen audited Sections 1–8 changed')
    for row in json.loads((ROOT/'SOURCE_FIDELITY.json').read_text())['unchanged_files']:
        need(sha((ROOT/row['public_path']).read_bytes())==row['sha256'], 'Frozen source mismatch: '+row['public_path'])
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for row in pins['sources']:
        data=(ROOT/row['path']).read_bytes()
        need(sha(data)==row['sha256'] and len(data)==row['bytes'], 'Source pin mismatch: '+row['path'])
        need(bool(re.fullmatch(r'https://github\.com/mxym/math/blob/[0-9a-f]{40}/.+', row['url'])), 'Unpinned source URL')
    ledger = json.loads((ROOT/'SANITIZATION_LEDGER.json').read_text())
    for row in ledger['derivatives']:
        need(sha((ROOT/row['path']).read_bytes())==row['after_sha256'], 'Sanitized derivative changed: '+row['path'])
        for edit in row['edits']:
            need(sha(edit['replacement'].encode())==edit['after_fragment_sha256'], 'Sanitization mapping mismatch')
    # New public-facing files must contain no private workspace locator.
    for name in FILES:
        if name.startswith('sources/') or name.endswith('.pdf'): continue
        content=(ROOT/name).read_text()
        for forbidden in ['/workspace/', '/home/agent/', '/root/', 'research_math/', 'sediment://', 'codex://']:
            # This checker necessarily names the patterns it rejects.
            if name=='check_package.py': continue
            need(forbidden not in content, 'Private locator in '+name)
    allowed = set(FILES+['MANIFEST.json','SHA256SUMS','source.zip'])
    for p in ROOT.rglob('*'):
        rel=p.relative_to(ROOT).as_posix()
        if any(rel.startswith(x) for x in ['build/','results/','__pycache__/']): continue
        if p.is_file(): need(rel in allowed, 'Unlisted payload file: '+rel)
    archive = ROOT/'source.zip'
    if archive.exists():
        need(archive.read_bytes()==archive_bytes(), 'Archive is not the exact deterministic payload')
        with zipfile.ZipFile(archive) as z:
            need(z.testzip() is None, 'Archive CRC failure')
    else:
        need(args.extracted, 'source.zip missing; use --extracted for an extracted archive')
    print(f'PASS: {len(FILES)} payload files; immutable mathematics, source pins, sanitized reports, checksums'+(' and deterministic archive.' if archive.exists() else '.'))

if __name__=='__main__': main()
