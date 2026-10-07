#!/usr/bin/env python3
"""Deterministically package the explicitly enumerated public payload."""
from pathlib import Path
import hashlib
import io
import json
import zipfile

ROOT=Path(__file__).resolve().parent
EPOCH=(2026,10,7,0,0,0)
FILES=['AUDITED_ORIGINAL_SOURCE_HASHES.json', 'INDEPENDENT_QUADRATIC_AUDIT.md', 'INTRINSIC_NORM_CONVERSION.md', 'MATHEMATICAL_DELTA.md', 'NOTICE.md', 'QUADRATIC_DIMENSION_THEOREM.md', 'README.md', 'RELEASE_SCOPE.json', 'SANITIZATION_LEDGER.json', 'SOURCE_FIDELITY.json', 'SOURCE_GUIDE.md', 'SOURCE_PINS.json', 'check_constants.py', 'check_independent_quadratic_audit.py', 'check_independent_refinement_audit.py', 'check_package.py', 'check_quadratic_constants.py', 'check_weighted_anchors.py', 'imports/POLYNOMIAL_REFINEMENT.md', 'imports/SQUARE_PYRAMID_LOWER_BOUND.md', 'imports/weighted_anchors.md', 'intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md', 'make_package.py', 'sources/HISTORICAL_SOURCE_PINS.json', 'sources/UPSTREAM_NOTICE.md', 'sources/entry005-v3.md', 'sources/openai_math_LICENSE.txt', 'sources/released-explicit-modulus.md', 'sources/sharp-simplex-proof.tex', 'sources/truncation-proof.tex', 'verification/check_independent_quadratic_audit.log', 'verification/check_independent_refinement_audit.log', 'verification/check_weighted_anchors.log', 'verification/constant_checks.json', 'verification/independent_exact_checks.json', 'verification/quadratic_constant_checks.json', 'verify.py']


def sha(data):return hashlib.sha256(data).hexdigest()


def archive_bytes():
    stream=io.BytesIO()
    with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_STORED) as archive:
        for name in sorted(FILES+['MANIFEST.json','SHA256SUMS']):
            info=zipfile.ZipInfo(name,EPOCH)
            info.create_system=3
            info.external_attr=0o100644<<16
            archive.writestr(info,(ROOT/name).read_bytes())
    return stream.getvalue()


def main():
    rows=[]
    for name in FILES:
        path=ROOT/name
        if path.is_symlink() or not path.is_file():raise RuntimeError('Missing/unsafe payload file: '+name)
        data=path.read_bytes();rows.append(dict(path=name,bytes=len(data),sha256=sha(data)))
    manifest=dict(schema='quadratic-public-package-v1',files=rows,scope='All release files except MANIFEST.json, SHA256SUMS, and source.zip. Generated results are excluded.')
    (ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    sums=''.join(sha((ROOT/name).read_bytes())+'  '+name+'\n' for name in sorted(FILES+['MANIFEST.json']))
    (ROOT/'SHA256SUMS').write_text(sums)
    data=archive_bytes();(ROOT/'source.zip').write_bytes(data)
    print(json.dumps(dict(archive='source.zip',bytes=len(data),sha256=sha(data),archive_entries=len(FILES)+2),indent=2))

if __name__=='__main__':main()
