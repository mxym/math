# Gaussian equal-mass simplex first moments: Lean progress, all k

**Partial formalization. The full all-k theorem is not proved.** This directory is an active coordination checkpoint, not a completed verification release.

The target is the sharp first-moment energy bound for actual measurable equal-mass Gaussian partitions, its almost-everywhere regular-simplex equality classification, the strict dimension obstruction, and the exact deficit identity. The mathematical baseline is [the fixed source commit](https://github.com/mxym/math/tree/890422e18fd7c80f3ce834426081211763cbc956).

The actual measure-theoretic, moment, optimal-price, flux, covariance and radial comparison chains are formalized. Regular-simplex attainment is unconditional. The full upper bound and equality classification still take the explicit proposition `GaussianMeasureBridge.EqualMassSimplicialPerimeterBound d` as an argument. This proposition is not a registered axiom. Its definition is in [GaussianPerimeterComparisonReduction.lean](sources/GaussianPerimeterComparisonReduction.lean); the conditional classification is in [GaussianRegularFanClassification.lean](sources/GaussianRegularFanClassification.lean).

The needed direction of the general simplicial BV/erosion bridge is now proved unconditionally for every full simplicial cell, in every dimension and at arbitrary prices: [actual_simplicial_cell_BV_upper](sources/GaussianSimplicialBVUpperBridge.lean). An original constructive route uses smooth transition products, dual normal directions and bounded-function Gaussian Stein identities; see [the route record](bv-development-route.json). Arbitrary unit-normal halfspaces additionally have exact BV/erosion equality. The sharp balanced-cluster BV lower bound remains a separate unproved geometric theorem. See [the explicit remaining obligation](perimeter-obligation.json) and [the natural interfaces](sources/GaussianBVComparisonInterface.lean). The bridge is an upper inequality; exact BV/erosion equality for general simplicial cells is not claimed.

The next development has proved the actual variational perimeter identities, finite-cluster lower semicontinuity under indicator-L1 convergence, a regular finite-BV competitor and a genuine bounded minimizing sequence. A supplied cellwise L1 limit preserves masses and the AE partition constraint and can be repaired to literally disjoint measurable cells; it gives an actual minimizing cluster. **The existence of that convergent subsequence is still unproved**, as are the remaining regularity/stability and sharp-minimum geometry. See [the minimization route](bv-minimization-route.json) and [the explicit compactness interface](sources/GaussianBVCompactnessInterface.lean). The profile upper bound from the regular competitor does not prove the sharp reverse inequality.

## Current evidence

All 132 source modules have successful development compilations matching their exact SHA-256 values. [STATUS.json](STATUS.json) gives the hashes, records and exact scope. Compiler output is preserved in `evidence/development/` with local paths normalized. These records are not a fresh independent verification of the whole project.

The prior frozen audit covered 53 matching modules, 528 owned declarations and their 59,703-declaration closure, replayed into an empty Lean kernel at trust level 0. That audit gives no credit to later source bytes. At the user's request, the unified fresh compilation, audit of every owned declaration and empty-kernel replay will occur after the entire mathematical proof is complete.

## Build the partial project

The official Lean toolchain is 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`; all nine dependencies are locked in `lake-manifest.json`.

With the official pinned toolchain installed, run these commands from this directory:

```sh
lake exe cache get
lake build
```

Use the supplied lock without running an unqualified `lake update`. These commands perform ordinary development compilation; they do not perform the deferred independent kernel replay. Dependency sources and caches are obtained from their official repositories and the official Mathlib cache service; no credentials are needed for this public project.

Do not reuse private absolute build paths or old compiled outputs as proof of new source bytes. `module-order.json` records a valid order of the current local imports. `SOURCE_MANIFEST.json` hashes this checkpoint's distributed files; the Git commit is its publication identity.
