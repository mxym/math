#!/bin/sh
# Run in a fresh temporary directory, so expected output is never overwritten.
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
tmp=$(mktemp -d)
printf '%s\n' "Replay directory: $tmp"
cd "$tmp"
export PYTHONDONTWRITEBYTECODE=1
${CXX:-g++} -std=c++17 -O3 "$src/census.cpp" -o census
${CXX:-g++} -std=c++17 -O3 "$src/witness_check.cpp" -o witness_check
./census 131 >GENERAL.txt 2>CENSUS.txt
python3 "$src/planar.py" >PLANAR.txt
python3 "$src/cover.py" >COVER.txt
python3 "$src/emit.py" >EMIT.txt
./witness_check >WITNESSES.txt
for f in CENSUS.txt GENERAL.txt PLANAR.txt COVER.txt EMIT.txt WITNESSES.txt; do
  cmp "$f" "$src/$f"
done
sha256sum -c "$src/GENERATED-SHA256SUMS"
cat WITNESSES.txt
