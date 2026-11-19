#!/bin/sh
# Run in a writable copy of the research directory.
set -eu
sha256sum -c SHA256SUMS
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT HUP INT TERM
cp bridge.py core-styles.txt small-masks.txt literal.cpp exhaust34.py check_small_alt.py GENERATED-SHA256SUMS "$d/"
p=$(pwd)
cd "$d"
python3 bridge.py > bridge.log
cmp bridge.log "$p/BRIDGE.txt"
sha256sum -c GENERATED-SHA256SUMS
${CXX:-c++} -std=c++17 -O2 literal.cpp -o literal
./literal > literal.log
cmp literal.log "$p/LITERAL.txt"
python3 exhaust34.py > exhaust.log
cmp exhaust.log "$p/EXHAUST34.txt"
python3 check_small_alt.py > alternate.log
cmp alternate.log "$p/ALTERNATE.txt"
cat bridge.log literal.log exhaust.log alternate.log
