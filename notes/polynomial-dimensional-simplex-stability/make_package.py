#!/usr/bin/env python3
"""Build deterministic integrity records and the self-contained source ZIP."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
EPOCH = (2026, 10, 7, 0, 0, 0)
FILES = sorted([
    'README.md', 'NOTICE.md', 'MATHEMATICAL_DELTA.md',
    'POLYNOMIAL_REFINEMENT.md', 'SQUARE_PYRAMID_LOWER_BOUND.md',
    'weighted_anchors.md', 'INDEPENDENT_REFINEMENT_AUDIT.md',
    'proof.tex', 'proof.pdf', 'build.sh', 'TYPESETTING_LEDGER.md', 'PDF_QA.json',
    'RELEASE_SCOPE.json', 'SOURCE_PINS.json', 'SOURCE_FIDELITY.json',
    'SANITIZATION_LEDGER.json', 'make_package.py', 'check_package.py', 'verify.py',
    'check_constants.py', 'check_weighted_anchors.py', 'check_independent_refinement_audit.py',
    'verification/constant_checks.json', 'verification/check_weighted_anchors.log',
    'verification/check_independent_refinement_audit.log',
    'sources/entry005-v2.md', 'sources/entry005-v3.md',
    'sources/sharp-simplex-proof.tex', 'sources/released-explicit-modulus.md',
    'sources/truncation-proof.tex', 'sources/UPSTREAM_NOTICE.md', 'sources/openai_math_LICENSE.txt',
])


def digest(data):
    return hashlib.sha256(data).hexdigest()


def archive_bytes():
    import io
    out = io.BytesIO()
    with zipfile.ZipFile(out, 'w', compression=zipfile.ZIP_STORED) as archive:
        for name in sorted(FILES + ['MANIFEST.json', 'SHA256SUMS']):
            info = zipfile.ZipInfo('polynomial-dimensional-simplex-stability/' + name, EPOCH)
            info.create_system = 3
            info.external_attr = (0o100755 if name.endswith('.sh') else 0o100644) << 16
            info.compress_type = zipfile.ZIP_STORED
            archive.writestr(info, (ROOT/name).read_bytes())
    return out.getvalue()


def main():
    rows = []
    for name in FILES:
        data = (ROOT/name).read_bytes()
        rows.append({'path':name, 'bytes':len(data), 'sha256':digest(data)})
    manifest = {
        'schema':'polynomial-dimensional-simplex-stability-public-manifest-v1',
        'date':'2026-10-07',
        'scope':'AI-assisted written mathematical supplement; independent analytic model audit; no human peer review or proof-assistant claim.',
        'excluded_integrity_self_references':['MANIFEST.json', 'SHA256SUMS', 'source.zip'],
        'files':rows,
    }
    data = (json.dumps(manifest, ensure_ascii=False, indent=2)+'\n').encode()
    (ROOT/'MANIFEST.json').write_bytes(data)
    sums = [(r['path'],r['sha256']) for r in rows]+[('MANIFEST.json',digest(data))]
    (ROOT/'SHA256SUMS').write_text(''.join(f'{h}  {n}\n' for n,h in sorted(sums)))
    data = archive_bytes()
    (ROOT/'source.zip').write_bytes(data)
    print(f'PASS: {len(FILES)} manifest files; source.zip {len(data)} bytes; SHA-256 {digest(data)}')

if __name__ == '__main__':
    main()
