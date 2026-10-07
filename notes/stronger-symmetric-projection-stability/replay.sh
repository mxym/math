#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build/replay results
python3 verify.py --output-dir build/replay/normal > build/replay/normal.txt
python3 verify.py --optimized --output-dir build/replay/optimized > build/replay/optimized.txt
cmp build/replay/normal/verification.json build/replay/optimized/verification-optimized.json
python3 check_independent.py > build/replay/independent.normal.txt
python3 -O check_independent.py > build/replay/independent.optimized.txt
cmp build/replay/independent.normal.txt build/replay/independent.optimized.txt
cp build/replay/normal/verification.json results/verification.json
cp build/replay/independent.normal.txt results/independent.txt
for name in matching halfmass geometry global; do
 cmp "build/replay/normal/$name.stdout.log" "build/replay/optimized/$name.optimized.stdout.log"
 cp "build/replay/normal/$name.stdout.log" "results/$name.txt"
done
head -n 1 build/replay/normal.txt
cat results/independent.txt
