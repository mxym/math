#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python3 verify-four-thirds-discretization.py
python3 verify-four-thirds-obstruction.py
