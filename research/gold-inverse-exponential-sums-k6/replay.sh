#!/bin/sh
set -eu
cd "$(dirname "$0")"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/gold-k6.XXXXXXXX")
trap 'rm -rf "$tmp"' 0
"${CXX:-c++}" -O3 -std=c++20 count_field.cc -o "$tmp/field"
"${CXX:-c++}" -O3 -std=c++20 count_recurrence.cc -o "$tmp/recurrence"
for k in 1 2 3 6
do
    "$tmp/field" "$k"
done > "$tmp/counts_field.txt"
for k in 1 2 3 6
do
    "$tmp/recurrence" "$k"
done > "$tmp/counts_recurrence.txt"
python3 verify.py "$tmp/counts_field.txt" "$tmp/counts_recurrence.txt"
