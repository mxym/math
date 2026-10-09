# Physical APPT necessity interface

`APPT.Quantum.density_appt_has_sorted_spectrum` accepts only an integer
`n >= 3`, a complex matrix on `Fin 3 x Fin n`, `IsDensity A`, and
`AbsolutelyPPT A`. The definitions are the actual PSD/trace-one and
all-global-unitaries partial-transpose definitions, not spectral surrogates.

It constructs `lam : Fin (3*n) -> Real` with descending order, nonnegative
entries, sum one, the exact identity `purity A = sum_i (lam i)^2`, and
both `matA`/`matB` PSD tests for every injective selection of nine indices.
No spectral-agreement, full-rank, strictly-positive-tail, Schmidt, or
Hildebrand-equivalence hypothesis is supplied. Zero eigenvalues are allowed.

The previously exported `CornerNecessity` and `SpectralData` modules supply
the physical nine-slot unitaries and actual sorted Hermitian spectrum.
This new interface packages their consequences together with normalization
and the second moment. It imports no uniform polynomial certificate module,
so downstream semantic work need not rebuild those large certificates.

## Verification

Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612` are fixed.

```sh
lake exe cache get
python3 reproduce_necessity.py --fresh
```

The runner checks the source hashes in `NECESSITY_SOURCES.json`, removes
only the local package build directory, builds the entire dependency target
`APPT.Quantum.SpectralNecessity`, checks a correct corner-slot assignment,
and requires an adjacent deliberately false assignment to be rejected with
its specific false-proposition diagnostic. A missing import or unrelated
compiler failure does not count as a successful negative control.

`NecessityReplay.lean` traverses the dependency closure of eleven theorem
roots and replays it from `mkEmptyEnvironment 0`. Missing constants,
unsafe/partial proof dependencies, and axioms other than `propext`,
`Classical.choice`, and `Quot.sound` are rejected. The roots' types and
universe parameters are compared after replay. Runtime and memory limits
are explicit in the runner; native proof evaluation is not used.

An initial WSL clean target build and paired controls passed, followed by
trust-zero replay of 34,435 declarations and eleven roots. The independent
GitHub workflow `appt-physical-necessity-lean.yml` runs the same proof target
and publishes literal source-bound records from `local-verification/necessity/`
as an artifact. A report certifies only the exact source hashes it lists;
the original WSL result is not presented as a later CI result.

## Scope and integration

This is the complete necessary semantic bridge for all integer n >= 3.
It does not assert the converse Hildebrand criterion. The concurrent
`LargeMaximum` module already proves the actual-state maximum `3/(8*n)`
for every n >= 9. Small-dimensional upper-bound assembly and the final
all-dimension package build/audit are separate work. Neither the interim
Release nor its files are changed; no full-formalization Release is created.
