#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python3 verify_independence_polynomial_rank_nine_minimum.py --with-envelope
python3 verify_independence_rank9_independent_local.py
python3 verify_independence_rank9_independent_envelope.py
