#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum --quiet -c SHA256SUMS
python3 verify_exact.py
python3 verify_independent.py
