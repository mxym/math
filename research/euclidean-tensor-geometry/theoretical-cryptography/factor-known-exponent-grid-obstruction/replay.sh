#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
actual=$(mktemp "${TMPDIR:-/tmp}/grid-obstruction.XXXXXX")
trap 'rm -f "$actual"' EXIT HUP INT TERM
python3 -I verify_grid_obstruction.py > "$actual"
diff -u RESULTS.txt "$actual"
cat "$actual"
