#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
sha256sum -c SHA256SUMS >/dev/null
result=$(mktemp "${TMPDIR:-/tmp}/c3-exact-lambda.XXXXXX")
trap 'rm -f "$result"' 0 HUP INT TERM
{
    python3 -I verify_exact.py
    python3 -I verify_independent.py
} >"$result"
diff -u RESULTS.txt "$result"
cat "$result"
