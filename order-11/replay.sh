#!/bin/sh
set -eu
cd "$(dirname "$0")"
base=${TMPDIR:-/tmp}
if [ -z "${TMPDIR:-}" ] && [ -d /dev/shm ] && [ -w /dev/shm ]; then
    base=/dev/shm
fi
tmp=$(mktemp -d "$base/qls11-replay.XXXXXX")
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
"${CXX:-c++}" -O3 -std=c++17 -Wall -Wextra classify.cpp -o "$tmp/c1"
"${CXX:-c++}" -O3 -std=c++17 -Wall -Wextra classify_independent.cpp -o "$tmp/c2"
# /dev/shm can be mounted noexec. In that case point TMPDIR at an executable directory.
"$tmp/c1" > "$tmp/a"
"$tmp/c2" > "$tmp/b"
awk 'NR>=3 {print $1,$3}' "$tmp/a" > "$tmp/h1"
awk 'NR>=4 {print $1,$3}' "$tmp/b" > "$tmp/h2"
diff -u "$tmp/h1" "$tmp/h2"
cat "$tmp/a" "$tmp/b"
python3 verify_explicit.py
