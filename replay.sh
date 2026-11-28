#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS >/dev/null
actual=$(mktemp)
trap 'rm -f "$actual"' EXIT HUP INT TERM
python3 verify_exact.py > "$actual"
python3 verify_independent.py >> "$actual"
diff -u RESULTS.txt "$actual"
cat "$actual"
