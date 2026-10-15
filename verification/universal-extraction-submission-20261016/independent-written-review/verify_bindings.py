"""Verify the compact review record and optionally its manuscript, read-only.

Only Python's standard library is required. Hash checks do not verify proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def basename(name):
    if not isinstance(name, str) or not name or Path(name).name != name or '/' in name or '\\' in name:
        raise ValueError('Binding must use a plain relative filename')
    return name


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manuscript', type=Path, help='Directory containing the eight TeX files and paper.pdf')
    args = parser.parse_args()
    review = Path(__file__).resolve().parent
    manifest = json.loads((review / 'PUBLIC_MANIFEST.json').read_text(encoding='utf-8'))
    for item in manifest['artifacts']:
        name = basename(item['path'])
        if digest(review / name) != item['sha256']:
            raise ValueError('Review file hash mismatch: ' + name)
    checked_manuscript = 0
    if args.manuscript is not None:
        bindings = json.loads((review / 'MANUSCRIPT_BINDINGS.json').read_text(encoding='utf-8'))
        for item in bindings['manuscript_files']:
            name = basename(item['path'])
            candidate = args.manuscript / name
            if not candidate.is_file() or digest(candidate) != item['sha256']:
                raise ValueError('Manuscript file missing or hash mismatch: ' + name)
            checked_manuscript += 1
    print(json.dumps({'review_files_verified': len(manifest['artifacts']),
                      'manuscript_files_verified': checked_manuscript,
                      'proof_verification_performed': False}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        # Keep diagnostic text independent of personal workspace locations.
        message = str(error) if isinstance(error, ValueError) else type(error).__name__
        print('Verification failed: ' + message, file=sys.stderr)
        sys.exit(1)
