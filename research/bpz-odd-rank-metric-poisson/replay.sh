#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 verify_finite.py
base=${TMPDIR:-/dev/shm}
work=$(mktemp -d "$base"/bpz-replay.XXXXXX)
trap 'rm -rf "$work"' EXIT HUP INT TERM
"${CXX:-c++}" -std=c++17 -O2 verify_intersection.cpp -o "$work/verify_intersection"
"$work/verify_intersection"
