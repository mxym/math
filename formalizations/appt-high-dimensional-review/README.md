# High-dimensional APPT: independent Lean review checkpoint

The package uses the actual complex density-matrix and all-global-unitary APPT definitions of the completed qutrit project. It does not replace them by an assumed spectral feasibility condition.

## Verified scope

The bounded fresh build passed for all local imported sources and the review modules. The original Lean declarations were then replayed into an empty kernel at trust level zero: **38,507 declarations and nine explicit roots**. Only `propext`, `Classical.choice`, and `Quot.sound` occur in their axiom closure. A deliberately forged proof of `density_appt_witness_posSemidef`, with its original type retained and proof replaced by `True.intro`, was rejected by that kernel.

- `Basic.lean`: left-factor/right-factor partial-transpose conventions are equivalent for PSD and APPT.
- `Hadamard.lean` and `QuantumWitness.lean`: a genuine unitary construction in every finite rectangular dimension; every permutation of the actual eigenvalues of an APPT density matrix yields the indicated PSD Schmidt-witness matrix.
- `Star.lean`: PSD star and least-diagonal star budgets, and a physical rectangular APPT star bound for specified labels.
- `SOS.lean`: the dimension-uniform scalar sum-of-squares inequality, exact counterexample purity comparisons, and the positive quartic certificate.
- `EntropyKernel.lean`: the actual logarithmic correction inequality, independently proved using two derivative/monotonicity arguments, and its strict exceptional-head barrier.

## What this does not certify

This is a PARTIAL formal review. It does not yet prove the unrestricted purity or entropy asymptotic theorem, the compactness/forest graph limits, their orders of limits and uniformity, the full exceptional-head entropy sum inequality, or the full arbitrary-dimension APPT membership of the new counterexample. The formal quantum bridge is a necessity theorem; it must not be presented as the missing sufficiency proof. No conclusion is assumed through a custom axiom, sorry, admit, or native_decide.

The analytic claims and statements need a separate proof-to-code coverage map as formalization grows. The existing frozen qutrit proof is a dependency, not certification of these later higher-dimensional results.

## Reproduction

Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned. From this directory, install/fetch the pinned dependencies with Lake and its Mathlib cache, then run:

```sh
python3 scripts/build_local.py Audit --fresh --timeout 240 --memory 8000
```

`LEAN_BIN` may name an explicit Lean binary. This runner recompiles the actual local import closure sequentially, bounds each invocation, and records literal logs and source/import-object hashes. It is not a substitute for the trust-zero replay executed in `Audit.lean`. A full `lake build` of this new package has not yet been recorded at this checkpoint; the completed bounded direct-Lean build and replay are the validation claimed here.

## Recovery and failure record

Unpushed files from the interrupted review were recovered, not silently treated as new verified work. The earlier audit command failed to parse because a multiline tactic call lacked `do`. This was repaired and the entire local dependency closure was freshly recompiled. The literal old failure logs and subsequent successful logs are retained in `verification/development/`; a failed attempt is not relabeled as a pass.

The checked proof logs and roots are in `verification/kernel/` and `verification/fresh-build.log`. `CHECKPOINT.json` records the successful source binding. The recovery was checked against public main 4248c2b2: every imported local Lean dependency source is byte-identical to that public source. No preprint, Release or prior manuscript was modified by this review.
