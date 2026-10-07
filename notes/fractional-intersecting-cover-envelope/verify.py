"""Verify frozen payload; replay exact diagnostics and optional scalar Lean."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    parser = ArgumentParser()
    parser.add_argument('--lean', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    for name, digest in manifest['files'].items():
        require(sha256((ROOT/name).read_bytes()).hexdigest() == digest, f'hash mismatch: {name}')
    lines = ''.join(f'{digest}  {name}\n' for name, digest in manifest['files'].items())
    require((ROOT/'SHA256SUMS').read_text() == lines, 'checksum inventory differs')
    print(f"Frozen inventory: {len(manifest['files'])} files PASS", flush=True)
    for flags in ([], ['-O']):
        subprocess.run([sys.executable, *flags, str(ROOT/'check_exact.py')], cwd=ROOT, check=True)
    if args.lean:
        source = (ROOT/'formal/FractionalCertificate.lean').read_text()
        require('sorry' not in source and 'native_decide' not in source, 'unproved proof escape')
        result = subprocess.run(['lake', 'env', 'lean', 'FractionalCertificate.lean'],
                                cwd=ROOT/'formal', check=True, text=True, capture_output=True)
        require(result.stderr == '' and 'sorryAx' not in result.stdout, 'unexpected Lean diagnostic')
        require(result.stdout == (ROOT/'results/lean-axioms.txt').read_text(), 'Lean export mismatch')
        print('Twelve Lean algebra exports and recorded axioms PASS', flush=True)


if __name__ == '__main__':
    main()
