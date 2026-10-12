#!/usr/bin/env bash
# Dependency paths come from the reviewer's pinned Mathlib environment.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
: "${LEAN_BIN:?Set LEAN_BIN to the absolute Lean 4.34.1 executable path}"
: "${MATHLIB_ROOT:?Set MATHLIB_ROOT to the absolute pinned Mathlib checkout path}"
: "${MATHLIB_LEAN_PATH:?Set MATHLIB_LEAN_PATH from the pinned Mathlib Lake environment}"
: "${CYCLOTOMIC_BUILD_DIR:?Set CYCLOTOMIC_BUILD_DIR to the fresh output directory}"
export LEAN_PATH
LEAN_PATH=$(python3 - <<'PY'
import os
from pathlib import Path
for key in ('LEAN_BIN', 'MATHLIB_ROOT', 'CYCLOTOMIC_BUILD_DIR'):
    if not Path(os.environ[key]).is_absolute():
        raise SystemExit(key + ' must be an absolute path')
root = Path(os.environ['MATHLIB_ROOT']).resolve()
paths = [Path(os.environ['CYCLOTOMIC_BUILD_DIR']).resolve()]
for entry in os.environ['MATHLIB_LEAN_PATH'].split(os.pathsep):
    if not entry:
        raise SystemExit('Empty dependency path entry is forbidden')
    p = Path(entry)
    paths.append((p if p.is_absolute() else root / p).resolve())
for p in paths:
    if not p.is_dir():
        raise SystemExit('Missing Lean import directory: ' + str(p))
    if os.pathsep in str(p):
        raise SystemExit('Path contains the import-list separator: ' + str(p))
print(os.pathsep.join(map(str, paths)))
PY
)
cd "$ROOT"
exec "$LEAN_BIN" "$@"
