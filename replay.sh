#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python3 verify_independence_polynomial_rank_growth.py
