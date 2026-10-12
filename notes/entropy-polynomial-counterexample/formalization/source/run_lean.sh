#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
OLD=$(cd "$ROOT/../crouzeix_lean_coverage_20261007" && pwd)
export ELAN_HOME="$OLD/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_PATH="${ENTROPY_BUILD_DIR:-$ROOT}:$(cd "$OLD/lean" && lake env printenv LEAN_PATH)"
cd "$ROOT"
exec "$ELAN_HOME/toolchains/leanprover--lean4---v4.34.1/bin/lean" "$@"
