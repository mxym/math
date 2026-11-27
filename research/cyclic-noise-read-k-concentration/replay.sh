#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ -f SHA256SUMS ]; then sha256sum -c SHA256SUMS >/dev/null; fi
python3 verify_exact.py
python3 verify_independent.py
