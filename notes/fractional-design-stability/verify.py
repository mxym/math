"""Replay the exact frozen proof payload and optional finite-incidence Lean."""
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
    expected = (ROOT/'results/exact.txt').read_text()
    for flags in ([], ['-O']):
        replay = subprocess.run([sys.executable, *flags, str(ROOT/'check_exact.py')],
                                cwd=ROOT, text=True, capture_output=True, check=True)
        require(replay.stderr == '' and replay.stdout == expected, 'exact diagnostic mismatch')
    print(expected, end='', flush=True)
    print('Normal and optimized exact replay agree PASS', flush=True)
    if args.lean:
        source = (ROOT/'formal/DesignCore.lean').read_text()
        require('sorry' not in source and 'native_decide' not in source, 'unproved proof escape')
        replay = subprocess.run(['lake', 'env', 'lean', 'DesignCore.lean'],
                                cwd=ROOT/'formal', text=True, capture_output=True, check=True)
        require(replay.stderr == '' and 'sorryAx' not in replay.stdout, 'unexpected Lean diagnostic')
        require(replay.stdout == (ROOT/'results/lean-axioms.txt').read_text(), 'Lean export mismatch')
        print('Seven finite incidence/converse Lean exports and axioms PASS', flush=True)


if __name__ == '__main__':
    main()
