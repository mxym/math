#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake env lean --version
lake build EntropyWakhare

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
lake env lean audit/AxiomsAudit.lean > "$scratch/axioms.txt"
python3 scripts/check_axioms.py "$scratch/axioms.txt"

if grep -R -n -E '(^|[^[:alnum:]_])(sorry|admit|native_decide|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' \
  EntropyWakhare.lean EntropyWakhare/*.lean; then
  echo 'FAIL: unchecked proof construct found'
  exit 1
fi

set +e
lake env lean audit/InvalidProof.lean > "$scratch/invalid-proof.txt" 2>&1
exit_code=$?
set -e
if [ "$exit_code" -eq 0 ]; then
  echo 'FAIL: Lean accepted invalid False proof'
  exit 1
fi
if ! grep -Eqi 'type mismatch|application type mismatch|has type|expected to have type' "$scratch/invalid-proof.txt"; then
  echo 'FAIL: invalid proof failed for a reason other than kernel rejection'
  cat "$scratch/invalid-proof.txt"
  exit 1
fi

echo 'PASS: intentionally invalid proof rejected by Lean'
echo 'PASS: full Wakhare entropy polynomial original formula has four distinct interior roots'
