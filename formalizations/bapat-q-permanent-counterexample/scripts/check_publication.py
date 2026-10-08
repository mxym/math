#!/usr/bin/env python3
"""Verify the complete public payload and its preserved compact evidence.

Every check remains active under python -O. This performs integrity checks,
not Lean compilation or kernel replay.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository-root', type=Path,
                        default=Path(__file__).resolve().parents[3])
    args = parser.parse_args()
    root = args.repository_root.resolve(strict=True)
    base = root / 'formalizations/bapat-q-permanent-counterexample'
    manifest_path = base / 'PUBLICATION_MANIFEST.json'
    manifest = json.loads(manifest_path.read_text())
    rows = manifest['files']
    listed = {row['path'] for row in rows}
    require(len(listed) == len(rows), 'Duplicate manifest path')
    expected = {str(p.relative_to(root)) for p in base.rglob('*')
                if p.is_file() and p != manifest_path}
    expected.add('notes/bapat-q-permanent-counterexample/LEAN_VERIFICATION_2026-10-08.md')
    require(listed == expected, 'Public file set differs from manifest')
    for row in rows:
        path = (root / row['path']).resolve(strict=True)
        require(path.is_relative_to(root), 'Unsafe manifest path')
        data = path.read_bytes()
        require(len(data) == row['bytes'], 'Size mismatch: ' + row['path'])
        require(hashlib.sha256(data).hexdigest() == row['sha256'],
                'SHA-256 mismatch: ' + row['path'])
        header = b'blob ' + str(len(data)).encode('ascii') + b'\0'
        require(hashlib.sha1(header + data).hexdigest() == row['git_blob_sha1'],
                'Git blob mismatch: ' + row['path'])
    with tempfile.TemporaryDirectory(prefix='bapat-publication-check-') as temp:
        result = subprocess.run([sys.executable, '-B', str(base / 'scripts/restore_evidence.py'),
                                 '--output', str(Path(temp) / 'evidence')], check=False)
        require(result.returncode == 0, 'Lossless evidence restoration check failed')
    print(json.dumps({'status': 'PASS', 'public_files_verified': len(rows),
                      'lean_executed': False, 'checks_active_under_python_optimization': True}))


if __name__ == '__main__':
    main()
