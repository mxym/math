#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS >&2
python3 verify_exact.py
python3 verify_independent.py
