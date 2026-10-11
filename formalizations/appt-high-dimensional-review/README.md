# High-dimensional APPT: independent mathematical review and Lean verification

**Partial formal verification. The full high-dimensional asymptotic purity, Renyi entropy, graph-limit, and rigidity theorems are not yet Lean-certified.** This package uses actual complex density matrices and the original all-global-unitary APPT definition.

## Newly closed physical-to-entropy bridge

`density_appt_paper_entropyHead` proves the nonlinear exceptional-head inequality for the actual canonically sorted eigenvalues, using exactly the paper pivot `b=lambda_(D-m(m+1)/2+1)` in one-based notation. Its hypotheses are only `m>=2`, `m<=n`, density, and APPT. The code constructs every eigenvalue permutation and rectangular corner embedding, proves pivot positivity from trace one, establishes all signs and ordering, derives the shifted-star budget, and invokes the previously checked logarithmic head theorem. No graph or head inequality is assumed in the physical statement.

`density_appt_entropyHead_at_pivot` proves the stronger admissible-pivot version. `appt_sorted_rankTwo_determinant` and `appt_largest_eigenvalue_bound` establish genuine ordered spectral consequences. `density_appt_singular_spectrum` starts from matrix determinant zero and proves that the eigenvalues are one zero and D-1 copies of 1/(D-1). The converse APPT attainment statement for that singular spectrum is not included in this new endpoint.

A kernel-audited regression constructs a genuine density matrix that is PPT but not APPT, so ordinary PPT is not silently substituted for the all-unitary hypothesis.

## Verification checkpoint

The fresh WSL Lake build completed **2,745 build tasks**. Trust-zero replay checked **40,088 transitive declarations and 22 explicit roots**. The only axioms were `propext`, `Classical.choice`, and `Quot.sound`. Replacing only the proof of `density_appt_paper_entropyHead` by `True.intro`, preserving its exact type, was rejected by the empty kernel. Thirty source/configuration files, including imported quantum definitions and the replay support, are SHA-256 bound. Literal logs and closure lists are in `verification/sorted-physical-20261011/`.

This checkpoint is a local fresh build and full empty-kernel replay, not yet an independent CI claim. A source-bound CI record, when available, is retained separately. The earlier independent run 38066697404 (991d4739) replayed 38,529 declarations and 13 roots with positional hypotheses; its evidence remains in `verification/ci-991d4739/` and is not relabeled as the newer result.

## Reproduction

Lean **4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** remain pinned. On Linux or WSL, with pinned dependencies cached:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

The runner checks both the source manifest and actual Mathlib checkout, builds only the review's imported closure rather than the full old 879-module package, compiles replay support with an explicit source root, runs physical regressions, and replays all audited roots. Every stage has a finite timeout; on timeout its entire process group is terminated and the literal failure output is retained. `--write-manifest` records intentional source changes and does not verify them.

## Review scope and failures

See `COVERAGE.md` and `REVIEW_20261011.md`. The previous named-permutation gap is closed for the sorted shifted-star and nonlinear-head theorem. General triangular placement, global graph asymptotics, counterexample sufficiency, final extrema and rigidity remain distinct unclosed formal obligations.

Recovered interrupted source work was recompiled before use. Its remaining entropy-wrapper tactic and inequality goals were repaired without new axioms or weakened hypotheses. An informational `ring_nf` suggestion in the successful build is not a failed theorem; success is determined by the compiler status and kernel replay. The earlier source-root audit failure is prevented by the explicit `--root` invocation. The memory-starved VPS was not used for these compilation jobs. No new preprint, Release, or high-dimensional completeness label is issued.
