# High-dimensional APPT: independent proof review

**Partial formal verification. The full high-dimensional asymptotic purity and entropy theorems are not yet Lean-certified.** This package uses the original complex density-matrix and all-global-unitary APPT definitions, not a substitute spectral model.

## Verified checkpoint recovered from the review branch

Independent GitHub Actions run **38066697404**, source **991d47393773140d36e1e6ee92b34bf87b07a715**, passed a Lake build of the imported closure (2,738 build tasks), followed by trust-zero replay of **38,529 declarations and 13 explicit roots**. The only axioms were `propext`, `Classical.choice`, and `Quot.sound`. Replacing the proof of the exact physical witness root by `True.intro`, without changing its type, was rejected. The uploaded proof modules and audit were byte-compared with the recovered source. Original logs, roots and workflow responses are in `verification/ci-991d4739/`.

The older main checkpoint b9056460 is retained separately. Its 38,507-declaration replay must not be confused with this later 38,529-declaration replay. The replaced source/audit entrypoints are preserved under `verification/checkpoint-b9056460/`, and the original historical logs remain available.

## Theorems checked

`Basic`, `Hadamard`, and `QuantumWitness` prove the transpose-convention bridge, the actual rectangular unitary construction, and positivity of every arbitrarily permuted eigenvalue witness for an actual Hermitian APPT matrix.

`Star` proves the arbitrary finite-dimensional PSD star inequality, retaining the central diagonal. Its physical wrappers derive the star budget from actual APPT matrices for specified eigenvalue labels.

`LogBounds` and `EntropyHead` prove inequalities for the actual real logarithm, including the singular endpoint, and the complete nonlinear exceptional-head sum bound. `appt_eigenvalue_entropyHead_bound` derives the required quadratic star budget from APPT, rather than assuming that budget as its conclusion. It still accepts a permutation and entrywise inequalities specifying the intended placement. Construction of the sorted-index placement from only dimension and sorting assumptions remains a separate obligation.

`SOS` checks the dimension-uniform scalar SOS, the positive quartic, and the exact rational purity gaps. It does **not** prove APPT membership of the 10x38 state; the generic quantum sufficiency bridge remains missing.

See `COVERAGE.md` for the current proof-to-code map. No forest/compactness theorem, unrestricted upper asymptotic, matching family, uniform limit, exact rectangular maximum or final entropy rigidity theorem is being relabeled as formally complete.

## Reproduce the checked checkpoint

Lean **4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** are pinned. From this directory with the pinned dependencies cached:

```sh
lake build APPTReview
mkdir -p .lake/build/lib/lean/Verification
lake env lean --root=../appt-qutrit-purity -o .lake/build/lib/lean/Verification/ReplaySupport.olean ../appt-qutrit-purity/Verification/ReplaySupport.lean
lake env lean -j1 -M6000 ReviewAudit.lean
```

The source root flag on the support invocation is essential. It is independent of the working directory and does not alter the theorem being checked. A bounded reproduction runner and additional regression tests are being reviewed separately; their mere presence is not a claim that they passed.

## Failure diagnosis

Early failed CI runs contained real elaboration errors in Hadamard coordinates, complex half-root normalization and star hypotheses. The passing source fixes those errors without adding assumptions or untrusted evaluators. Run **38065695262** is different: its 2,704-target Lake build succeeded, but compiling `Verification/ReplaySupport.lean` failed because the source file lay outside Lean's default root. The corrected explicit `--root` invocation passed in run **38066697404**. Warnings and a tactic diagnostic from an attempted branch are not being mistaken for the actual terminal failure.

The local VPS has insufficient available memory for efficient further compilation; a stopped bounded import test is not a mathematical failure. No source-theorem completion is inferred from elapsed time, finite regression counts or a green job unrelated to the exact source.
