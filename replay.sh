#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python3 verify-kissing-thirty-point-flattening.py
python3 verify-kissing-bipartite-stress.py
