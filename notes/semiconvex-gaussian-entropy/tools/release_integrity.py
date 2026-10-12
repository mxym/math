#!/usr/bin/env python3
"""Regenerate release integrity records only after deliberate review of edits."""
from pathlib import Path
import hashlib, importlib.util, json
ROOT=Path(__file__).resolve().parent.parent
PATHS=sorted([
    'AUDIT_VERIFICATION.json','MANIFEST.json','ORIGINAL_INPUT_HASHES.json','PROVENANCE.json',
    'PUBLICATION_WHITELIST.json','README.md','SHA256SUMS','SOURCE_MANIFEST.json','SOURCE_MAP.md',
    'TECHNICAL_AUDIT.md','VERIFICATION.json','checks/check_correction.py','checks/check_exact.py',
    'checks/correction_replay.json','checks/independent_checks.py','checks/independent_replay.json',
    'checks/original_replay.json','entropy.tex','fetch_sources.py','originals/entropy.corrected.tex',
    'originals/entropy.tex','paper.pdf','public_editorial.patch','source.tar.gz','sources.json',
    'square_exponential_domain.patch','tools/build_pdf.sh','tools/release_integrity.py','verify.py'])
GENERATED={'MANIFEST.json','PUBLICATION_WHITELIST.json','SHA256SUMS','SOURCE_MANIFEST.json','source.tar.gz'}
found=set()
for path in ROOT.rglob('*'):
    if path.is_symlink(): raise RuntimeError('Symlink is not a release file')
    if path.is_file(): found.add(path.relative_to(ROOT).as_posix())
if found-GENERATED != set(PATHS)-GENERATED:
    raise RuntimeError('Missing or unexpected payload files: '+str(found.symmetric_difference(set(PATHS))))
def write(name,value):
    (ROOT/name).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def entry(path):
    data=(ROOT/path).read_bytes()
    return {'path':path,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
write('PUBLICATION_WHITELIST.json',{'root':'notes/semiconvex-gaussian-entropy','paths':PATHS,
    'scope':'Only these exact release files; no external-paper PDFs, source caches or build outputs.'})
source_paths=sorted(set(PATHS)-{'MANIFEST.json','SHA256SUMS','paper.pdf','source.tar.gz'})
write('SOURCE_MANIFEST.json',{'description':'Canonical source archive payload; excludes this manifest from its own hash list.',
    'files':[entry(path) for path in source_paths if path!='SOURCE_MANIFEST.json']})
spec=importlib.util.spec_from_file_location('verify',ROOT/'verify.py')
module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
(ROOT/'source.tar.gz').write_bytes(module.source_archive(source_paths))
write('MANIFEST.json',{'description':'All release files except this manifest and SHA256SUMS; SHA256SUMS hashes this manifest.',
    'files':[entry(path) for path in PATHS if path not in {'MANIFEST.json','SHA256SUMS'}]})
(ROOT/'SHA256SUMS').write_text(''.join(hashlib.sha256((ROOT/path).read_bytes()).hexdigest()+'  '+path+'\n' for path in PATHS if path!='SHA256SUMS'))
print('PASS: exact whitelist, canonical source archive and integrity records generated.')
