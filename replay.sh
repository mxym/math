#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python3 verify_factor_lehmer_exact_mod_three.py
python3 verify_factor_lehmer_small_mod_three.py 8 10
python3 verify_factor_lehmer_mod_three_independent.py
