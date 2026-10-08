#!/usr/bin/env python3
"""Package complete source-only proof delivery; no toolchain, cache or owned olean."""
from pathlib import Path
import hashlib
import json
import shutil
import stat
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'delivery/entry005-actual-pyramid-20261007'
if DEST.exists():
    shutil.rmtree(DEST)
DEST.mkdir(parents=True)
selected = [ROOT / 'README.md', ROOT / 'TECHNICAL_REPORT.md', ROOT / 'coverage.json']
selected += [p for p in (ROOT / 'formal').rglob('*') if p.is_file()
             and '.lake' not in p.parts and '__pycache__' not in p.parts]
selected += [ROOT / 'scripts' / name for name in
             ['bootstrap.sh', 'verify_pyramid.py', 'test_pyramid_audits.py', 'package_pyramid.py',
              'replay_text_bundle.py']]
# All exact source/provenance tables; exclude development snapshots and obsolete interim patches.
source_names = ['proof.tex', 'entry005-v2-paper.md', 'published-note-README.md', 'provenance.json',
    'HISTORICAL_INITIAL_INSPECTION.md', 'UPSTREAM_NOTICE.md', 'PYRAMID_UPSTREAM_REUSE.md',
    'openai_math_LICENSE.txt', 'pyramid-provenance.json', 'openai-projection-source-inventory.json',
    'frozen-147-source-hashes.json', 'frozen-147-theorems.json', 'coverage-frozen147.json',
    'new-pyramid-source-hashes.json', 'owner-unchanged-source-hashes.json',
    'owner-joint-interface-hashes.json', 'owner-iid-helper-provenance.json',
    'owner-iid-helper-exact-body-check.json',
    'all-public-theorems.json', 'all-public-theorems-by-module.json',
    'pyramid-all-public-theorems.json', 'pyramid-theorems-by-module.json',
    'cache-extract-manifest.json', 'arbitrary-cache-extract-manifest.json',
    'arbitrary-missing-cache-modules.json', 'pyramid-82-verified.patch', 'pyramid-82-manifest.json']
selected += [ROOT / 'sources' / name for name in source_names]
selected += [p for p in (ROOT / 'sources/openai-math').rglob('*') if p.is_file()]
selected += [ROOT / 'logs' / name for name in
    ['pyramid-clean-build-release.log', 'pyramid-verify-release.log', 'pyramid-verification.json',
     'pyramid-clean-714-statements.log', 'pyramid-clean-82-statements.log',
     'pyramid-clean-owned-declarations.log', 'pyramid-clean-owned-closure.log',
     'pyramid-clean-public-declarations.log', 'pyramid-pins.log', 'pyramid-pins-optimized.log',
     'pyramid-guard-controls.log', 'pyramid-guard-controls-optimized.log']]
selected += sorted((ROOT / 'logs').glob('pyramid-control-*.log'))
for p in sorted(set(selected)):
    if not p.is_file():
        raise RuntimeError('Required delivery file absent: ' + str(p))
    target = DEST / p.relative_to(ROOT)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(p, target)
    target.chmod(stat.S_IMODE(p.stat().st_mode))
manifest = [{'path': p.relative_to(DEST).as_posix(), 'bytes': p.stat().st_size,
             'mode': stat.S_IMODE(p.stat().st_mode), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in sorted(DEST.rglob('*')) if p.is_file()]
(DEST / 'SOURCE_FILES_SHA256.json').write_text(json.dumps(manifest, indent=2) + '\n')
archive = ROOT / 'delivery/entry005-actual-pyramid-20261007.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for p in sorted(DEST.rglob('*')):
        if p.is_file():
            z.write(p, arcname=p.relative_to(DEST.parent).as_posix())
with zipfile.ZipFile(archive) as z:
    if z.testzip() is not None:
        raise RuntimeError('Archive CRC validation failed')
    for item in manifest:
        data = z.read(DEST.name + '/' + item['path'])
        if hashlib.sha256(data).hexdigest() != item['sha256']:
            raise RuntimeError('Archive file mismatch')
info = {'archive': str(archive), 'bytes': archive.stat().st_size,
        'sha256': hashlib.sha256(archive.read_bytes()).hexdigest(), 'file_count': len(manifest) + 1}
(ROOT / 'delivery/archive-info.json').write_text(json.dumps(info, indent=2) + '\n')
print(json.dumps(info, indent=2))
