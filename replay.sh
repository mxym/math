#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python3 verify_ryser_six_twenty_four_edges.py
python3 verify_ryser_six_twenty_three_edges.py
python3 verify_ryser_23_independent.py
