# Qutrit-qudit APPT purity: all-dimension Lean proof

**The actual all-n maximal-purity theorem has compiled and passed independent
trust-zero kernel replay. Final release validation is in progress.**
Run `37956727424` passed all 879 local modules, the default Lake build, and a
155,787-declaration / 58-root replay. A later auxiliary endpoint test failed
arithmetic simplification; that test is corrected and the final forged-proof
control is being rerun. See
[the exact checkpoint boundary](verification/all-n-kernel-checkpoint-20261009/README.md).
No full-formalization Release is claimed at this checkpoint.

## Mathematical statement and physical semantics

For every natural number `n >= 3`, the maximum of `Tr(rho*rho)` over the
absolutely-PPT density matrices on `C^3 tensor C^n` is

```text
(3*n + 8)/(3*n + 2)^2,  if 3 <= n <= 8;
3/(8*n),               if n >= 9.
```

`APPT.Quantum.appt_purity_maximum_formula` states this as
`IsGreatest (attainablePurities n) (...)`. Consequently the result contains both
a universal upper bound and an actual attaining state, not just a supremum.

The definitions in `APPT/Quantum/Basic.lean` use the genuine objects:
`IsDensity A` means `A.PosSemidef` and `A.trace = 1`;
`AbsolutelyPPT A` requires positivity of the partial transpose after conjugation
by **every global complex unitary**; and `purity A` is `(A*A).trace.re`.
There are no unproved A/B-matrix, spectral, or Schmidt-decomposition hypotheses
in the final theorem.

## Paper-to-Lean proof map

| Mathematical obligation | Lean declarations/modules |
| --- | --- |
| Actual unitary orbits and partial transpose | `Quantum.Basic`, `Quantum.Orbit`, `Quantum.Reindex` |
| APPT implies the required corner PSD conditions | `Quantum.CornerNecessity`: `diagonal_appt_necessary_matrices`; `Quantum.SpectralNecessity`: `density_appt_has_sorted_spectrum` |
| Sorted nonnegative eigenvalues and actual diagonalization | `Quantum.SpectralData` |
| Trace normalization and trace-square spectral identity | `Quantum.SpectralMoments` |
| Six finite spectral upper bounds | `Finite9Bound` through `Finite24Bound`, `SpectrumBound9` through `SpectrumBound24` |
| Uniform certificate for the whole large-dimension family | `Uniform.normalized_bound`, `UniformBridge.arbitrary_middle_bound`, `ordered_spectrum_large` |
| Small actual-state upper bound | `Quantum.SmallMaximum`: `appt_purity_upper_small`, for every 3 <= n <= 8 |
| Large actual-state upper bound | `Quantum.LargeMaximum`: `appt_purity_upper_large`, for every n >= 9 |
| Actual APPT attaining states in both branches | `Quantum.Attainment`: `targetPurity_attained` |
| Final attained maximum for every n >= 3 | `Quantum.Maximum`: `appt_purity_maximum_formula` |

The corner-necessity bridge is proved with explicit physical unitaries. A full
classification of APPT spectra by a Hildebrand if-and-only-if criterion is not
needed: necessity supplies the upper bound, while direct quantum constructions
prove the required attaining states are APPT. No missing equivalence is assumed.

The small-branch witness is `(I+2vv*)/(3*n+2)` for a unit vector. The large-branch
witness is `(I+P)/(4*n)` for a rank-n coordinate projection. Normalization,
positivity, all-unitary APPT, and the trace-square values are proved in Lean.
These witnesses establish attainment, not a classification of all equality cases.

## Bounded exact certificates

The original 1,635-term uniform rational certificate and all six finite
certificates are retained. Python generates exact integer coefficient data;
Lean proves every identity and every sign. `ring` handles small symbolic
identities, and `decide +kernel` checks exact finite coefficient operations.
No `native_decide`, `sorry`, `admit`, or custom axiom is used in the proof closure.

The finite generator now inserts independently proved literal coefficient
barriers and explicit `nat_lit` / integer constructors. This avoids expensive
repeated overloaded-numeral elaboration without changing coefficient values
or theorem statements. Deterministic regeneration reproduces 600 finite Lean
files plus their manifest, and 229 uniform Lean files plus their manifest. The complete import graph has 879 local
modules, and the proof/tool inventory pins 942 files.

The completed component build recorded every module under a 300-second limit;
the largest recorded module took 239.703 seconds. In the independent dense-D24
probe, two formerly timed-out modules took 22.044 and 20.168 seconds and passed
trust-zero replay. See [the bounded coefficient audit](BOUNDED_COEFFICIENT_AUDIT.md).

## Verification, negative controls, and trust boundary

`CheckpointReplay.lean` collects the explicit theorem roots and their transitive
closure, rejects unsafe/partial declarations and unapproved axioms, and replays
them in an initially empty Lean kernel at trust level zero. It also compares
replayed root types and universe parameters with the originals. The only allowed
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`CompletionAudit.lean` additionally replaces the proof of the **same final
maximum theorem** by `True.intro` and requires a second fresh kernel to reject
it for a declaration type mismatch. The auxiliary sparse, corner, and endpoint
controls pair a valid statement with deliberately invalid data; timeouts or
unrelated compiler errors do not count as successful rejection.

[The all-dimension physical semantic regression](SEMANTIC_REGRESSION.md) proves
that a genuine PPT density state can have purity one and fail APPT for every
n >= 3. Thus ordinary PPT cannot silently replace the final theorem's APPT
hypothesis. It passed a separate 35,589-declaration trust-zero replay.

External dependency caches and hash-bound component objects accelerate builds;
they are not proof oracles. Reports distinguish fresh project builds from
component reuse. The final mathematical closure is independently rechecked at
trust zero even when object caches are used.

## Reproduce

Pinned toolchain: Lean **4.34.1**. Pinned Mathlib:
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

From this directory:

```sh
lake exe cache get
python3 scripts/source_manifest.py --check
python3 reproduce.py --fresh --jobs 2
```

`--fresh` removes only this package's `.lake/build`, retaining external dependency
caches. Omitting it permits source/object-hash-bound resumption, which is recorded
as such. The script enforces individual module limits, runs the complete default
Lake target, checks regeneration, tests correct and incorrect certificates,
and performs both kernel audits. Literal results go to `local-verification/complete/`.
A source manifest is checked, not regenerated as part of verification.

## Scope and provenance

This proof covers the exact APPT purity maximum for all qutrit-qudit systems with
n >= 3. It does not assert a classification of all maximizers, the corresponding
separability optimum, arbitrary first-factor dimension, or cases n < 3.
It makes no new novelty, priority, or external peer-review claim.

The parallel `appt-qutrit-purity-lean` work supplied modular reindexing; the actual
source is retained here. Finite data originated in the interim package. The
immutable `appt-qutrit-purity-interim-v1` Release and its files are not modified.
Historical audit reports remain historical; they do not replace the full-theorem
verification records.
