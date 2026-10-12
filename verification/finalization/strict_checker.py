#!/usr/bin/env python3
"""Run a published checker with assertions enabled, even under python -O.

The historical checker bytes are unchanged. compile(..., optimize=0) is
deliberate: several exact finite checkers use assert as a proof obligation.
This launcher does not convert finite diagnostics into universal proofs.
"""
import argparse
from pathlib import Path
import sys
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('checker', type=Path)
    args = parser.parse_args()
    path = args.checker.resolve(strict=True)
    if sys.flags.optimize:
        # Also preserve assertions in imported local helper modules. Merely
        # compiling the entrypoint with optimize=0 does not cover its imports.
        raise SystemExit(subprocess.call([sys.executable,'-I','-B',
                                         str(Path(__file__).resolve()),str(path)]))
    sys.path.insert(0, str(path.parent))
    sys.argv = [str(path)]
    namespace = {'__name__': '__main__', '__file__': str(path),
                 '__package__': None, '__builtins__': __builtins__}
    exec(compile(path.read_bytes(), str(path), 'exec', optimize=0), namespace)


if __name__ == '__main__':
    main()
