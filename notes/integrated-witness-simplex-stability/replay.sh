#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build/replay results
python3 check_integrated.py --output build/replay/certificate.normal.json > build/replay/check.normal.txt
python3 -O check_integrated.py --output build/replay/certificate.optimized.json > build/replay/check.optimized.txt
cmp build/replay/certificate.normal.json build/replay/certificate.optimized.json
cmp certificate.json build/replay/certificate.normal.json
cmp build/replay/check.normal.txt build/replay/check.optimized.txt
python3 check_independent.py > build/replay/independent.normal.txt
python3 -O check_independent.py > build/replay/independent.optimized.txt
cmp build/replay/independent.normal.txt build/replay/independent.optimized.txt
cp build/replay/check.normal.txt results/check.txt
cp build/replay/independent.normal.txt results/independent.txt
cat results/check.txt results/independent.txt
