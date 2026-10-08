#!/usr/bin/env python3
"""Package only the explicit publication candidate; exclude local build/QA caches."""
from pathlib import Path
import gzip, hashlib, io, json, tarfile
root = Path(__file__).resolve().parent
base = [
    '.gitignore', 'README.md', 'SOURCE_MAP.md', 'SOURCE_MAP.json', 'BUILD_INFO.md',
    'QA.md', 'INTEGRITY_CHECK.json', 'REPRODUCIBILITY.json', 'preamble.tex',
    'build.sh', 'verify_bundle.py', 'reproduce.py', 'package.py',
    'sources/top-n.PROOF.md', 'sources/binary-mass.PROOF.md',
    'sources/general-moment.PROOF.md', 'sources/general-moment.before-repair.PROOF.md',
    'review/REVIEW.md', 'review/ORIGINAL_VERDICT.json',
    'review/LIMITED_RECHECK.md', 'review/LIMITED_RECHECK.json',
    'review/endpoint-repair.diff',
]
for paper in ['top-n', 'binary-mass', 'general-moment']:
    base += [f'{paper}/main.tex', f'{paper}/body.tex', f'{paper}/main.pdf']
base = sorted(base)
sha = lambda p: hashlib.sha256((root / p).read_bytes()).hexdigest()
files = sorted(base + ['PUBLICATION_FILE_LIST.json', 'SHA256SUMS'])
manifest = {
    'status': 'Publication candidate only; no publication performed',
    'date': '2026-10-08', 'publication_files': files,
    'payload_sha256': {p: sha(p) for p in base},
    'hash_scope': 'payload_sha256 excludes this manifest and SHA256SUMS to avoid recursion. SHA256SUMS additionally hashes this manifest.',
    'excluded': ['build directories', 'TeX dependency/cache trees', 'raw compiler logs', 'rendered page images', 'local replay directories', 'archive itself'],
}
(root / 'PUBLICATION_FILE_LIST.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
(root / 'SHA256SUMS').write_text(''.join(sha(p) + '  ' + p + '\n' for p in sorted(base + ['PUBLICATION_FILE_LIST.json'])))
archive = root / 'transport-stability-series-20261008.tar.gz'
with archive.open('wb') as output:
    with gzip.GzipFile(filename='', mode='wb', fileobj=output, mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode='w', format=tarfile.PAX_FORMAT) as tar:
            for path in files:
                data = (root / path).read_bytes()
                info = tarfile.TarInfo('transport-stability-series-20261008/' + path)
                info.size = len(data)
                info.mtime = 1791417600
                info.uid = info.gid = 0
                info.uname = info.gname = ''
                info.mode = 0o755 if path in ['build.sh', 'verify_bundle.py', 'reproduce.py', 'package.py'] else 0o644
                tar.addfile(info, io.BytesIO(data))
checksum = hashlib.sha256(archive.read_bytes()).hexdigest()
(root / (archive.name + '.sha256')).write_text(checksum + '  ' + archive.name + '\n')
print(json.dumps({'archive': archive.name, 'sha256': checksum, 'bytes': archive.stat().st_size, 'files': len(files)}, indent=2))
