"""Check frozen payload and replay exact diagnostics, optionally Lean."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = ArgumentParser()
    parser.add_argument('--lean', action='store_true')
    args = parser.parse_args()
    inventory = json.loads((ROOT/'MANIFEST.json').read_text())
    for name, expected in inventory['files'].items():
        require(sha256((ROOT/name).read_bytes()).hexdigest() == expected, f'hash mismatch: {name}')
    expected = ''.join(f'{digest}  {name}\n' for name, digest in inventory['files'].items())
    require((ROOT/'SHA256SUMS').read_text() == expected, 'checksum list mismatch')
    print(f"Frozen inventory: {len(inventory['files'])} files PASS", flush=True)
    for flags in ([], ['-O']):
        subprocess.run([sys.executable, *flags, str(ROOT/'checks/check_exact.py')], check=True, cwd=ROOT)
    if args.lean:
        source = (ROOT/'formal/DefectCertificate.lean').read_text()
        require('sorry' not in source and 'native_decide' not in source, 'unexpected proof escape')
        result = subprocess.run(['lake', 'env', 'lean', 'DefectCertificate.lean'],
                                check=True, cwd=ROOT/'formal', text=True, capture_output=True)
        require('sorryAx' not in result.stdout+result.stderr, 'unproved Lean placeholder')
        require(result.stdout == (ROOT/'results/lean-axioms.txt').read_text(), 'Lean export drift')
        require(result.stderr == '', 'unexpected Lean diagnostic')
        print('Six Lean exports replayed; exact recorded axioms PASS', flush=True)


if __name__ == '__main__':
    main()
