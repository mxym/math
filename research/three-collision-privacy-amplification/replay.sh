#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
python3 -B verify_moments.py
python3 -B verify_ranks_exponents.py
