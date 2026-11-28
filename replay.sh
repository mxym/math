#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export LC_ALL=C.UTF-8
sha256sum -c SHA256SUMS
diff -u RESULTS.txt <(python3 verify_exact.py && python3 verify_independent.py)
cat RESULTS.txt
