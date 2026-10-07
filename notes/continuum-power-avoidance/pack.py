#!/usr/bin/env python3
"""Deterministically rebuild source and release integrity metadata offline."""
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def main():
    here = Path(__file__).resolve().parent
    payload = sorted([
        'ORIGINAL_INPUT_HASHES.json', 'PINNED_SOURCE_VERIFICATION.json',
        'PROOF.txt', 'PROOF_MAP.json', 'PROVENANCE.json', 'README.md',
        'REFERENCE_MANIFEST.json', 'TECHNICAL_AUDIT.txt', 'VERIFICATION.json',
        'checks/check_exact.py', 'checks/independent_oracles.py',
        'checks/submitted_expected.json', 'checks/independent_expected.json',
        'pack.py', 'paper.tex', 'verify.py',
        'sources/006-v1-main.tex', 'sources/006-v2-paper.md',
        'sources/084-main.tex', 'sources/084-03-windows.tex',
        'sources/084-04-routing.tex', 'sources/084-05-scales.tex',
        'sources/mxym-NOTICE.md', 'sources/openai_math_LICENSE.txt',
    ])
    rows = []
    for name in payload:
        data = (here / name).read_bytes()
        rows.append({'path': name, 'bytes': len(data), 'sha256': sha(data)})
    members = sorted(payload + ['SOURCE_MANIFEST.json'])
    write(here / 'SOURCE_MANIFEST.json', {
        'description': 'Source archive payload. This manifest is included as an archive member and excluded from its own hash list.',
        'hashed_source_file_count': len(rows), 'archive_member_count': len(members),
        'archive_members': members, 'files': rows})
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode='w', format=tarfile.USTAR_FORMAT) as tar:
        for name in members:
            data = (here / name).read_bytes()
            item = tarfile.TarInfo(name)
            item.size = len(data)
            item.mode = 0o644
            item.mtime = item.uid = item.gid = 0
            item.uname = item.gname = ''
            tar.addfile(item, io.BytesIO(data))
    compressed = io.BytesIO()
    with gzip.GzipFile(fileobj=compressed, mode='wb', filename='', mtime=0) as gz:
        gz.write(out.getvalue())
    (here / 'source.tar.gz').write_bytes(compressed.getvalue())
    allowed = sorted(members + ['paper.pdf', 'source.tar.gz', 'MANIFEST.json', 'PUBLICATION_WHITELIST.json'])
    write(here / 'PUBLICATION_WHITELIST.json', {'description': 'Complete approved public-copy paths; excludes logs, caches, render images, and private transfer metadata.', 'files': allowed})
    actual = sorted(str(p.relative_to(here)) for p in here.rglob('*') if p.is_file())
    expected_now = sorted(name for name in allowed if name != 'MANIFEST.json' or (here / name).exists())
    if actual != expected_now:
        raise RuntimeError('Unexpected file outside the explicit public whitelist')
    rows = []
    for name in allowed:
        if name == 'MANIFEST.json':
            continue
        data = (here / name).read_bytes()
        rows.append({'path': name, 'bytes': len(data), 'sha256': sha(data)})
    write(here / 'MANIFEST.json', {'description': 'Complete release payload except this manifest itself.', 'files': rows})
    print(json.dumps({'source_hashed_files': len(payload), 'source_archive_members': len(members),
                      'release_files': len(allowed), 'archive_sha256': sha(compressed.getvalue())}, sort_keys=True))


if __name__ == '__main__':
    main()
