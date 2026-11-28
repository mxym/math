#!/bin/sh
set -eu
export LC_ALL=C
sha256sum -c SHA256SUMS
actual=$(python3 -B verify_finite.py)
expected=$(sed -n '2p' RESULTS.txt)
printf '%s\n' "$actual"
test "$actual" = "$expected"
printf '%s\n' "PASS: digest manifest and recorded finite replay agree"
