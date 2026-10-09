# APPT qutrit–qudit: quantum and uniform-certificate continuation

**IN PROGRESS. This is not yet the complete maximal-purity theorem.**
This additive working package does not modify the immutable
`appt-qutrit-purity-interim-v1` Release or its files.

## Proved quantum theorem

For every finite second-factor index type and every complex matrix `P` on
`Fin 3 × b`, if `P` and `1-P` are positive semidefinite, then
`partialTranspose P + 1` is positive semidefinite. Moreover `1+P` is
**absolutely PPT**: partial transposition is positive after every global
unitary conjugation. The definition quantifies over the actual complex
unitary group; it does not replace APPT with a spectral condition.

`Quantum/Contractions.lean` gives an explicit identity expressing
`partialTranspose P + 1` as a sum of nine PSD congruences of `P` and
`1-P`. The symmetric/antisymmetric local two-plane matrices give the
identity without an unproved Hildebrand criterion or Schmidt decomposition.
`Quantum/Orbit.lean` proves preservation under unitary conjugation and
nonnegative scaling, and invariance of actual trace-square purity.

## Uniform certificate infrastructure

`CoefficientMerge.lean` proves that merging sparse integer coefficient
lists preserves evaluation over the real numbers. This separates small
polynomial expansions from large integer arithmetic. Concrete coefficient
identities use `decide +kernel`, not native evaluation. The full 1,635-term
certificate is being checked in a separate bounded-module build and is
**not yet an exported theorem of this checkpoint**.

## Remaining mathematical work

The all-dimension certificate, its complete ordered-spectrum application,
APPT-to-A/B necessity, the rank-one attaining orbit for the small-dimension
branch, the normalized attaining states and final state-level maximum
remain unassembled here. The positive-contraction orbit theorem supplies
one substantive part of the long-dimension attainment argument, not the
entire optimality result. No full formalization Release is created.

A parallel continuation in `../appt-qutrit-purity-lean/` maintains the
outer/middle reindexing and gap modules. This package uses a distinct path
and namespace submodules to avoid overwriting that work. The original
finite-certificate sources are in `../appt-qutrit-purity-interim/`.

## Reproduce

Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

```sh
lake exe cache get
python3 reproduce.py
```

The runner builds the complete default Lake target, replays the explicit
root closure from an empty kernel environment at trust level zero, checks
the allowed axiom names, and executes both a correct and an incorrect
coefficient control. The failed control alone is not evidence of a
working checker: its neighboring positive control must pass too.
The runner writes literal logs and source hashes to `local-verification/`.
Recorded evidence identifies the exact checked source hashes.
