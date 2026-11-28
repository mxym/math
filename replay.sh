#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python3 verify-kissing-nine-gram-cells.py census
python3 127_independent_graph_census.py
python3 127_independent_budget.py
python3 verify-kissing-nine-gram-cells.py 7
python3 verify-kissing-nine-gram-cells.py 9
node verify-kissing-127-reciprocal-barrier.js
