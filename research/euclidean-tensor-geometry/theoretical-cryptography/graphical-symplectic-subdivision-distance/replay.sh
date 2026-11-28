#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS >/dev/null
python3 verify_exact.py
python3 verify_independent.py
