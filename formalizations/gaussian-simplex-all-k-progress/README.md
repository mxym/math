# Gaussian equal-mass simplex first moments: Lean progress, all k

**Partial formalization. The full all-k theorem is not proved.** This directory is an active coordination checkpoint, not a completed verification release.

The target is the sharp first-moment energy bound for actual measurable equal-mass Gaussian partitions, its almost-everywhere regular-simplex equality classification, the strict dimension obstruction, and the exact deficit identity. The mathematical baseline is [the fixed source commit](https://github.com/mxym/math/tree/890422e18fd7c80f3ce834426081211763cbc956).

The actual measure-theoretic, moment, optimal-price, flux, covariance and radial comparison chains are formalized. Regular-simplex attainment is unconditional. The full upper bound and equality classification still take the explicit proposition `GaussianMeasureBridge.EqualMassSimplicialPerimeterBound d` as an argument. This proposition is not a registered axiom. Its definition is in [GaussianPerimeterComparisonReduction.lean](sources/GaussianPerimeterComparisonReduction.lean); the conditional classification is in [GaussianRegularFanClassification.lean](sources/GaussianRegularFanClassification.lean).

The current geometric work proves the bridge from actual simplicial cells to variational Gaussian BV perimeter. Arbitrary unit-normal halfspaces and two-cell fans are already proved. An original constructive route uses smooth transition products, dual normal directions and bounded-function Gaussian Stein identities; see [the route record](bv-development-route.json). The sharp balanced-cluster BV lower bound remains a separate unproved geometric theorem. See [the explicit remaining obligation](perimeter-obligation.json) and [the natural interfaces](sources/GaussianBVComparisonInterface.lean).

## Current evidence

All 114 source modules have successful development compilations matching their exact SHA-256 values. [STATUS.json](STATUS.json) gives the hashes, records and exact scope. Compiler output is preserved in `evidence/development/` with local paths normalized. These records are not a fresh independent verification of the whole project.

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
