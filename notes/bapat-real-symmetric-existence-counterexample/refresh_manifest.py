#!/usr/bin/env python3
"""Hash the deliberately small release payload, without circular self-hashes.
Local render images, auxiliary files, and preparatory drafts are not published.
"""
from hashlib import sha1, sha256
import json
from pathlib import Path

root = Path(__file__).resolve().parent
names = {'paper.pdf', 'paper.tex', 'proof.md', 'README.md', 'SOURCES_AND_REVIEW.md',
         'PROOF_DEPENDENCIES.md', 'build.sh', 'export_markdown.py',
         'refresh_manifest.py', 'build-pass2.log', 'qa/QA_REPORT.md'}
for pattern in ['review/*.md', 'verification/*.py', 'verification/*.log']:
    names.update(p.relative_to(root).as_posix() for p in root.glob(pattern))
entries = []
for rel in sorted(names):
    p = root / rel
    if not p.is_file():
        raise SystemExit(f'Missing release file: {rel}')
    data = p.read_bytes()
    entries.append({'path': rel, 'bytes': len(data), 'sha256': sha256(data).hexdigest(),
                    'git_blob_sha1': sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()})
manifest = {
    'title': "Real symmetric counterexamples to Bapat's q-permanent conjecture",
    'date_utc': '2026-10-08',
    'scope': 'Finite existence; integer real symmetric positive-definite counterexample; no explicit numerical real witness or dimension bound.',
    'proof_assistant_certification': False,
    'external_human_peer_review_claimed': False,
    'third_party_paper_pdf_included': False,
    'pdf_pages': 9,
    'review_note': 'See SOURCES_AND_REVIEW.md and the reports for exact inspected source versions.',
    'files': entries,
    'excluded_local_material': ['PNG page renders', 'LaTeX auxiliary files', 'bbox and text extraction intermediates', 'preparatory proof draft', 'first-pass TeX log', 'checksum run log'],
    'self_hash_policy': 'The manifest excludes itself and SHA256SUMS. SHA256SUMS includes the manifest, excludes itself.'
}
(root / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
checks = [(e['path'], e['sha256']) for e in entries]
checks.append(('MANIFEST.json', sha256((root / 'MANIFEST.json').read_bytes()).hexdigest()))
(root / 'SHA256SUMS').write_text(''.join(f'{h}  {name}\n' for name, h in sorted(checks)))
print(f'Wrote manifest for {len(entries)} payload files and checksums for {len(checks)} files.')
