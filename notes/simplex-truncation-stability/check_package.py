#!/usr/bin/env python3
"""Read-only integrity check, active under python3 -O. Build products are ignored."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import sys
import zipfile

ROOT = Path(__file__).resolve().parent


def require(test, message):
    if not test:
        raise RuntimeError(message)


def digest(path):
    data = path.read_bytes()
    return len(data), hashlib.sha256(data).hexdigest()


def main():
    require(sys.argv[1:] in ([], ['--extracted']), 'Only --extracted is supported')
    extracted = bool(sys.argv[1:])
    names = (ROOT / 'PACKAGE_FILES.txt').read_text().splitlines()
    require(names == sorted(set(names)), 'Whitelist must be sorted and duplicate-free')
    for name in names:
        p = PurePosixPath(name)
        require(bool(name) and not p.is_absolute() and '..' not in p.parts and str(p) == name, 'Unsafe whitelist path')
    expected = set(names) - ({'source.zip'} if extracted else set())
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file()
              and p.relative_to(ROOT).parts[0] not in {'build', '__pycache__'}}
    # A re-created archive is permitted in an extracted tree.
    if extracted:
        actual.discard('source.zip')
    require(actual == expected, 'Package whitelist mismatch: missing=' + repr(sorted(expected-actual)) + '; extra=' + repr(sorted(actual-expected)))
    for name in actual:
        require(not (ROOT / name).is_symlink(), 'Symlink is not an archive payload: ' + name)
    m = json.loads((ROOT / 'MANIFEST.json').read_text())
    excluded = {'MANIFEST.json', 'source.zip'}
    require(m['excluded_to_avoid_self_reference'] == sorted(excluded), 'Unexpected manifest exclusion')
    payload = {entry['path']: entry for entry in m['files']}
    require(len(payload) == len(m['files']), 'Duplicate manifest path')
    require(set(payload) == set(names)-excluded, 'Manifest does not cover the complete payload')
    for name, entry in payload.items():
        require(digest(ROOT/name) == (entry['bytes'], entry['sha256']), 'Hash or size mismatch: ' + name)
    sources = json.loads((ROOT/'sources/SOURCE_MANIFEST.json').read_text())
    for entry in sources['files']:
        require(digest(ROOT/entry['local_path']) == (entry['bytes'], entry['sha256']), 'Pinned source mismatch: ' + entry['local_path'])
    if (ROOT/'source.zip').is_file():
        with zipfile.ZipFile(ROOT/'source.zip') as archive:
            expected_members = ['simplex-truncation-stability/'+name for name in names if name != 'source.zip']
            require(archive.namelist() == expected_members, 'Archive membership/order differs from whitelist')
            require(archive.testzip() is None, 'Archive CRC failure')
            for name in names:
                if name != 'source.zip':
                    require(archive.read('simplex-truncation-stability/'+name) == (ROOT/name).read_bytes(), 'Archive byte mismatch: '+name)
    else:
        require(extracted, 'source.zip missing')
    print(f'Package integrity passed: {len(payload)} payload hashes; {len(sources["files"])} pinned-source records; exact whitelist.')


if __name__ == '__main__':
    main()
