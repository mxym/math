#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
sha256sum -c SHA256SUMS >/dev/null
actual=$(python3 verify_exact.py && python3 verify_independent.py)
expected=$(cat RESULTS.txt)
if [ "$actual" != "$expected" ]; then
    printf '%s\n' "$actual" >&2
    exit 1
fi
printf '%s\n' "$actual"
