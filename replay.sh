#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
for f in verify_*.py; do python3 "$f"; done
