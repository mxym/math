# High-dimensional APPT: independent mathematical review and Lean verification

**Partial formal verification. The full high-dimensional asymptotic purity, Renyi entropy, graph-limit, and rigidity theorems are not yet Lean-certified.** This package uses actual complex density matrices and the original all-global-unitary APPT definition.

## New arbitrary-dimensional sufficiency and attainment

The new finite theorem `absolutelyPPT_dimension_contraction` proves that `(m-1)I+2P` is APPT whenever the actual complex bipartite matrix P and its complement I-P are positive semidefinite. The first-factor index is an arbitrary finite type; the theorem does not assume a Schmidt decomposition, a spectral criterion, or positivity of the partial transpose as a hypothesis. Its proof is a dimension-uniform identity expressing `2 partialTranspose(P)+(m-1)I` as a sum of positive congruences of P and I-P.

`exists_projectionPlateau` constructs an actual density/APPT matrix for every rank k between zero and mn, with purity `[mn(m-1)^2+4mk]/[mn(m-1)+2k]^2`. `exists_broad_plateau` specializes this to k=ceil((m-1)n/2), including its dimension and rank bounds. These are physical ATTAINMENT statements, not the unrestricted upper bound or equality classification of the rectangular maximum theorem.

The antisymmetric projection proves the dimension constant is sharp in square systems. An additional audited regression is the actual 4x4 density matrix `(I+P_antisymmetric)/22`, which is not APPT: the dimension-three formula I+P cannot simply be reused in dimension four. The positive regression constructs a 4x58 APPT density matrix with purity exactly 2/435.

The new source passed a fresh WSL Lake build of 2,749 tasks and trust-zero replay of 40,214 declarations with 34 roots. Only the standard three axioms were present. Replacing the proof of `exists_broad_plateau` by `True.intro` was rejected. All 34 pinned inputs transferred to this revision match the audited WSL bytes, including the imported physical definitions. Independent CI **38131356027**, source **adcf334861438cf0ffc83b39ee5fedfe7e086447**, has now passed the same fresh build and replay. Literal logs, the 34-input committed-source binding, 40,214-declaration closure and all physical regressions are retained in `verification/ci-adcf3348/`. The older independent record below is separate historical evidence.

## Newly closed physical-to-entropy bridge

`density_appt_paper_entropyHead` proves the nonlinear exceptional-head inequality for the actual canonically sorted eigenvalues, using exactly the paper pivot `b=lambda_(D-m(m+1)/2+1)` in one-based notation. Its hypotheses are only `m>=2`, `m<=n`, density, and APPT. The code constructs every eigenvalue permutation and rectangular corner embedding, proves pivot positivity from trace one, establishes all signs and ordering, derives the shifted-star budget, and invokes the previously checked logarithmic head theorem. No graph or head inequality is assumed in the physical statement.

`density_appt_entropyHead_at_pivot` proves the stronger admissible-pivot version. `appt_sorted_rankTwo_determinant` and `appt_largest_eigenvalue_bound` establish genuine ordered spectral consequences. `density_appt_singular_spectrum` starts from matrix determinant zero and proves that the eigenvalues are one zero and D-1 copies of 1/(D-1). The converse APPT attainment statement for that singular spectrum is not included in this new endpoint.

A kernel-audited regression constructs a genuine density matrix that is PPT but not APPT, so ordinary PPT is not silently substituted for the all-unitary hypothesis.

## Verification checkpoint

The fresh WSL Lake build completed **2,745 build tasks**. Trust-zero replay checked **40,088 transitive declarations and 22 explicit roots**. The only axioms were `propext`, `Classical.choice`, and `Quot.sound`. Replacing only the proof of `density_appt_paper_entropyHead` by `True.intro`, preserving its exact type, was rejected by the empty kernel. Thirty source/configuration files, including imported quantum definitions and the replay support, are SHA-256 bound. Literal logs and closure lists are in `verification/sorted-physical-20261011/`.

Independent GitHub Actions run **38127581602**, source **a3201c675616a8caf330786933171e424659a7eb**, has now passed the same fresh build, regressions and trust-zero replay: 2,745 build tasks, 40,088 declarations and 22 roots. The uploaded sources and all thirty committed input files were checked against their pins. Literal source-bound CI evidence is retained separately in `verification/ci-a3201c67/`. The earlier independent run 38066697404 (991d4739) replayed 38,529 declarations and 13 roots with positional hypotheses; its evidence remains in `verification/ci-991d4739/` and is not relabeled as the newer result.

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

## Ordered paired-gap upper bound

`density_appt_pair_gap_square_sum` now proves the actual sorted APPT bound `sum_(i=1)^R (lambda_i-lambda_(D+1-i))^2 <= 8*b^2`, with the exact paper pivot and no supplied graph or eigenvalue-placement hypothesis. General pair arrangements, squared matrix-action bounds and the dimension-uniform triangular row estimate are formalized. The local fresh replay passed with 41,929 declarations and 45 roots. See `REVIEW_TRIANGULAR_20261011.md`; independent CI evidence is recorded only after checking the matching remote run. The full centered finite purity inequality and all asymptotic extrema remain separate unclosed obligations.

Independent CI **38136186474** on **7e74ae8e** has now passed: 2,829 build tasks, 41,929 trust-zero declarations, 45 roots, and rejection of a corrupted proof of the actual paired-gap theorem. All 42 pinned inputs and uploaded proof/tool files matched. Literal evidence is retained in `verification/ci-7e74ae8e/`.
