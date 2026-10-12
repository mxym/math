#!/usr/bin/env python3
"""Build byte manifest and deterministic archive from the fixed package whitelist."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent


def whitelist():
    names = (ROOT / 'PACKAGE_FILES.txt').read_text().splitlines()
    if len(names) != len(set(names)) or names != sorted(names):
        raise RuntimeError('Whitelist must be sorted and duplicate-free')
    for name in names:
        p = PurePosixPath(name)
        if not name or p.is_absolute() or '..' in p.parts or str(p) != name:
            raise RuntimeError('Unsafe whitelist path: ' + name)
    if not {'MANIFEST.json', 'source.zip', 'PACKAGE_FILES.txt'} <= set(names):
        raise RuntimeError('Required package control file absent from whitelist')
    return names


def main():
    names = whitelist()
    excluded = {'MANIFEST.json', 'source.zip'}
    records = []
    for name in names:
        if name in excluded:
            continue
        p = ROOT / name
        if p.is_symlink() or not p.is_file():
            raise RuntimeError('Missing or nonregular payload: ' + name)
        b = p.read_bytes()
        records.append({'path': name, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
    manifest = {
        'schema': 'mxym-math-package-manifest-v1',
        'entry': '005',
        'supplement': 'integrated-witness-simplex-stability',
        'date': '2026-10-07',
        'entry005_definition_ref': '31e3d8a37e4a3051a7f5a2535be1c75642e15bcc',
        'quantitative_supplement_ref': '6785c1c830f8e19e2eb07b0bb89f4d475a8b154a',
        'scope': 'Byte identity only; mathematical correctness rests on the written proof. No publication action is performed by packaging.',
        'excluded_to_avoid_self_reference': sorted(excluded),
        'archive_root': 'integrated-witness-simplex-stability',
        'files': records,
    }
    (ROOT / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    with zipfile.ZipFile(ROOT / 'source.zip', 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name in names:
            if name == 'source.zip':
                continue
            info = zipfile.ZipInfo('integrated-witness-simplex-stability/' + name, date_time=(2026, 10, 7, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, (ROOT / name).read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    print(f'Wrote {len(records)} payload hashes and {len(names)-1} archive entries.')
    print('source.zip SHA256: ' + hashlib.sha256((ROOT / 'source.zip').read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
