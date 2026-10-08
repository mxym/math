#!/usr/bin/env python3
"""Restore the exact 141-file compact evidence tree from lossless public parts.

Writes only to a previously nonexistent output directory outside this package.
Checks are explicit and remain active under python -O. This never executes Lean.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

BASE = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def checked_bytes(root, row):
    path = (root / row['path']).resolve(strict=True)
    require(path.is_relative_to(root.resolve()), 'Unsafe storage path')
    data = path.read_bytes()
    require(len(data) == row['bytes'], 'Stored size mismatch: ' + row['path'])
    require(hashlib.sha256(data).hexdigest() == row['sha256'],
            'Stored hash mismatch: ' + row['path'])
    return data


def restore(output):
    output = output.resolve()
    require(not output.exists(), 'Output directory already exists')
    require(not output.is_relative_to(BASE), 'Output must be outside the public package')
    projection = json.loads((BASE / 'PUBLIC_PROJECTION.json').read_text())
    require(projection['restored_files'] == 141, 'Unexpected compact file count')
    retained = projection['retained_files']
    packed = projection['packed_files']
    names = [row['path'] for row in retained] + [row['path'] for row in packed]
    require(len(names) == len(set(names)) == 141, 'Duplicate or missing restored path')
    expected = {row['path'] for row in retained}
    actual = {str(p.relative_to(BASE / 'evidence')) for p in (BASE / 'evidence').rglob('*')
              if p.is_file()}
    require(actual == expected, 'Retained evidence file set mismatch')
    payload = {}
    for row in retained:
        payload[row['path']] = checked_bytes(BASE / 'evidence', row)
    for row in packed:
        compressed = b''.join(checked_bytes(BASE, part) for part in row['parts'])
        require(len(compressed) == row['packed_bytes'], 'Packed size mismatch')
        require(hashlib.sha256(compressed).hexdigest() == row['packed_sha256'],
                'Packed hash mismatch')
        if row['encoding'] == 'gzip':
            data = gzip.decompress(compressed)
        elif row['encoding'] == 'identity':
            data = compressed
        else:
            raise RuntimeError('Unknown storage encoding')
        require(len(data) == row['bytes'], 'Restored size mismatch: ' + row['path'])
        require(hashlib.sha256(data).hexdigest() == row['sha256'],
                'Restored hash mismatch: ' + row['path'])
        payload[row['path']] = data
    for name in payload:
        require((output / name).resolve().is_relative_to(output), 'Unsafe restored path')
    output.mkdir(parents=True, exist_ok=False)
    for name, data in payload.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    result = subprocess.run([sys.executable, '-B', str(output / 'reproduce.py'),
                             '--check-only'], check=False)
    require(result.returncode == 0, 'Restored compact evidence failed original checks')
    print(json.dumps({'status': 'PASS', 'restored_files': len(payload),
                      'source_files': 22, 'lean_executed': False}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    restore(args.output)


if __name__ == '__main__':
    main()
