#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
out=$(python3 verify_exact.py && python3 verify_independent.py)
printf '%s\n' "$out"
expected=$(cat RESULTS.txt)
test "$out" = "$expected"
