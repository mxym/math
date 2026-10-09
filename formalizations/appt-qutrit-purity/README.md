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

## Completed uniform certificate and ordered-spectrum upper bound

`Uniform.normalized_bound`, `UniformBridge.arbitrary_middle_bound`, and
`ordered_spectrum_large` now compile. They cover every real endpoint
population `t,z≥0`, `t+z≥18`, and every sorted normalized nonnegative
spectrum of total dimension at least 27, under the displayed A/B PSD
conditions. This is an infinite-dimensional family, not a table of tests.

The original 1,635 positive rational terms are retained exactly. Each
small generator expansion is proved with `ring`; large integer coefficient
merges are checked with `decide +kernel`, using the proved evaluation
lemmas in `CoefficientMerge` and `CoefficientMergeFast`. No native proof
evaluation is used. The checked module dependency graph has 232 modules,
all passing a 180-second per-module bound in the recorded direct Lean run.
The roots including the ordered-spectrum bound passed trust-zero empty
kernel replay of 45,051 declarations. Portable regeneration reproduces
all 230 generated files byte for byte.

The full default Lake build was previously recorded for attainment.
A fresh bounded Lake build including the uniform extension is now part
of `reproduce.py`; the earlier attainment Lake evidence is not presented
as evidence for that larger build. Updated Lake evidence will be retained
when the larger run completes.

## Complete attainment direction

`Quantum/Attainment.lean:targetPurity_attained` proves for every integer
`n≥3` that an actual trace-one PSD complex matrix is absolutely PPT and
has purity `(3n+8)/(3n+2)^2` for `n≤8`, or `3/(8n)` for `n≥9`.
The first branch uses `(I+2vv*)/(3n+2)` with a normalized vector; the
second uses `(I+P)/(4n)` with a rank-n coordinate projection.
Both proofs quantify over every global unitary.

The pure-projector bound `I+2*partialTranspose(vv*)≥0` is proved using an
explicit three-column skew Gram identity and a rectangular-contraction
lemma. It does not use an assumed Schmidt decomposition or Hildebrand
criterion. Normalization, matrix squaring, trace, and purity are proved
inside Lean, not supplied as witness hypotheses.

## Remaining mathematical work

**The actual-state upper bound and final maximum theorem are not yet
exported here.** The uniform ordered-spectrum upper bound and both actual
APPT attaining branches are complete in the exported sources. Necessary
A/B matrices have additionally been obtained from physical unitary corner
conjugations in the development tree; the matrix diagonalization/sorted
spectrum assembly remains to be integrated and audited. No full
formalization Release is created.

A parallel continuation in `../appt-qutrit-purity-lean/` maintains the
outer/middle reindexing and gap modules. This package uses a distinct path
and namespace submodules to avoid overwriting that work. The original
finite-certificate sources are in `../appt-qutrit-purity-interim/`.

The spectrum sum reindexing module is reused from the parallel package at
commit `39764a6`; its source is retained and freshly compiled here.

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
