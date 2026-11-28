#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS >&2
for script in verify_exact.py verify_independent.py; do
    python3 "$script"
done
