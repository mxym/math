#!/bin/sh
# Checks run on a private copy because check_exact.py writes beside itself.
set -eu
cd "$(dirname "$0")"
mkdir -p build/replay
cp check_exact.py build/replay/check_exact.py
python3 build/replay/check_exact.py >build/replay/normal.txt
cp build/replay/exact_certificate.json build/replay/normal.json
python3 -O build/replay/check_exact.py >build/replay/optimized.txt
cmp build/replay/normal.txt build/replay/optimized.txt
cmp build/replay/normal.json build/replay/exact_certificate.json
cmp exact_certificate.json build/replay/exact_certificate.json
cmp exact_run.txt build/replay/normal.txt
cmp exact_run.optimized.txt build/replay/optimized.txt
printf '%s\n' 'Normal and optimized exact replay passed; archived certificates and logs match.'
