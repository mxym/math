#!/usr/bin/env bash
# Fresh local compilation and axiom audit; does not perform empty-kernel replay.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT"
python3 check_sources.py
: "${LEAN_BIN:?Set LEAN_BIN to the absolute Lean 4.34.1 executable path}"
: "${MATHLIB_ROOT:?Set MATHLIB_ROOT to the absolute pinned Mathlib checkout path}"
: "${MATHLIB_LEAN_PATH:?Set MATHLIB_LEAN_PATH from the pinned Mathlib Lake environment}"
export LEAN_BIN MATHLIB_ROOT MATHLIB_LEAN_PATH
VERSION=$("$LEAN_BIN" --version)
printf '%s\n' "$VERSION" | grep -Eq 'version 4\.34\.1([, ]|$)'
PIN=$(git -C "$MATHLIB_ROOT" rev-parse HEAD)
[[ "$PIN" == d13f23b723b8a846827a245b89c10fc7d3f11612 ]]
[[ -z "$(git -C "$MATHLIB_ROOT" status --porcelain --untracked-files=no)" ]]
mkdir -p "$ROOT/.verification-runs"
RUN=$(mktemp -d "$ROOT/.verification-runs/run.XXXXXX")
export CYCLOTOMIC_BUILD_DIR="$RUN/olean"
mkdir "$CYCLOTOMIC_BUILD_DIR"
printf '%s\n%s\n' "$VERSION" "$PIN" > "$RUN/pins.log"
printf 'Run directory: %s\n' "$RUN"
: > "$RUN/cleancompile.log"
: > "$RUN/completed-modules.txt"
for module in CoefficientList CyclotomicFormulas PrimeExclusion BasicProperties Expansion DataProperties Counterexample CenteredCertificate; do
  printf '\n=== %s ===\n' "$module" >> "$RUN/cleancompile.log"
  bash run_lean.sh -o "$CYCLOTOMIC_BUILD_DIR/$module.olean" "$module.lean" >> "$RUN/cleancompile.log" 2>&1
  printf '%s\n' "$module" >> "$RUN/completed-modules.txt"
done
bash run_lean.sh Audit.lean > "$RUN/finaltheorem-signatures-and-axioms.log" 2>&1
bash run_lean.sh BasicPropertiesAudit.lean > "$RUN/basic-properties-audit.log" 2>&1
bash run_lean.sh PrimeExclusionAudit.lean > "$RUN/prime-exclusion-audit.log" 2>&1
python3 audit_sources.py "$RUN"
