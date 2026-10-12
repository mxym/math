#!/usr/bin/env bash
# Strict end-to-end replay of the compiled universal cycle theorem.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo 'Lean version:'
lake env lean --version

echo 'Build all eleven owned proof modules and the public theorem entrypoint:'
lake build ChromaticCyclesAllN

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
lake env lean audit/AxiomsAudit.lean > "$scratch/axioms.txt"
python3 scripts/check_axioms.py "$scratch/axioms.txt"

if grep -R -n -E '(^|[^[:alnum:]_])(sorry|admit|native_decide|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' \
    ChromaticCyclesAllN.lean ChromaticCyclesAllN/*.lean; then
    echo 'FAIL: prohibited proof placeholder / unchecked construct'
    exit 1
fi

set +e
lake env lean audit/InvalidProof.lean > "$scratch/invalid-proof.txt" 2>&1
exit_code=$?
set -e
if [[ "$exit_code" -eq 0 ]]; then
    echo 'FAIL: Lean accepted intentionally invalid proof'
    exit 1
fi
if ! grep -Eq 'type mismatch|application type mismatch|has type|expected to have type' "$scratch/invalid-proof.txt"; then
    echo 'FAIL: invalid proof failed for an unexpected reason'
    cat "$scratch/invalid-proof.txt"
    exit 1
fi

echo 'PASS: incorrect proof rejected by Lean kernel'
echo 'PASS: complete graph-coloring-to-chromatic-polynomial classification verified'
