#!/bin/sh
set -eu
cd "$(dirname "$0")"
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT HUP INT TERM
CXX=${CXX:-c++}
"$CXX" -std=c++17 -O3 -DNDEBUG weights_forward.cpp -o "$t/w1"
"$CXX" -std=c++17 -O3 -DNDEBUG weights_reverse.cpp -o "$t/w2"
"$t/w1" > "$t/w1.txt"
"$t/w2" > "$t/w2.txt"
cmp "$t/w1.txt" weights.txt
cmp "$t/w2.txt" weights.txt
"$CXX" -std=c++17 -O3 -DNDEBUG charts_forward.cpp -o "$t/c1"
"$t/c1" < "$t/w1.txt" > "$t/f"
cmp "$t/f" forward_ledger.txt
grep '^raw ' "$t/f" > "$t/r"
cmp "$t/r" charts.txt
python3 -O charts_reverse.py "$t/w2.txt" "$t/terminal" > "$t/r2"
cmp "$t/r2" charts.txt
cmp "$t/terminal" terminal_certificates.txt
echo "PASS: two 348-profile generations; two 32-chart exhaustive searches; 30 cubic and two quintic contradictions"
