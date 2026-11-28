#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
actual=$(mktemp "${TMPDIR:-/tmp}/lambda-two-odd-primes.XXXXXX")
trap 'rm -f "$actual"' EXIT HUP INT TERM
python3 -I verify_lambda_two_odd_primes.py > "$actual"
diff -u RESULTS.txt "$actual"
cat "$actual"
