#!/usr/bin/env python3
"""Check package byte identity, not mathematical truth."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    files = manifest.get('files')
    if not isinstance(files, list) or not files:
        raise RuntimeError('No files in manifest')
    seen = set()
    for row in files:
        relative = row['path']
        path = (ROOT / relative).resolve()
        if relative in seen or not path.is_relative_to(ROOT) or not path.is_file():
            raise RuntimeError('Invalid, duplicate or missing path: ' + relative)
        seen.add(relative)
        blob = path.read_bytes()
        if len(blob) != row['bytes'] or hashlib.sha256(blob).hexdigest() != row['sha256']:
            raise RuntimeError('Byte mismatch: ' + relative)
    print('PASS:', len(files), 'package files match their sizes and SHA-256 hashes.')
    print('Scope: byte identity only; theorem correctness requires the written proof.')

if __name__ == '__main__':
    main()
