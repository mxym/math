#!/usr/bin/env python3
"""Verify the published v3 bytes and pinned inherited proof inputs."""
from pathlib import Path
import hashlib
import json


def main():
    root=Path(__file__).resolve().parents[1]
    repo=root.parents[2]
    data=json.loads((root/'MANIFEST.json').read_text())
    count=0
    for category,base in [('files',root),('dependencies',repo)]:
        for relative,expected in data[category].items():
            path=(base/relative).resolve()
            if not path.is_relative_to(base.resolve()):
                raise ValueError('manifest path leaves its declared root')
            actual=hashlib.sha256(path.read_bytes()).hexdigest()
            if actual!=expected:
                raise ValueError(f'hash mismatch: {relative}')
            count+=1
    print(f'PASS: {count} version-file and inherited-input SHA-256 hashes')
    print('SCOPE: byte identity only; not a certificate of theorem correctness.')


if __name__=='__main__':
    main()
