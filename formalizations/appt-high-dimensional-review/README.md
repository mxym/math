## New fixed-local result: independent audit pending

The new source proves the fixed-m limit of the supremum over actual APPT density matrices, including matching physical projection states and explicit errors. It also closes the upper half uniformly over all dimension pairs as total dimension grows. Individual development compilations passed; no independent verification of this newly extended source is claimed until its fresh build and kernel audit finish. The older verified checkpoints below retain their original scopes.

See `REVIEW_FIXED_LOCAL_20261011.md` for the exact normalization, supremum definition, finite bounds, quantifiers and remaining obligations. No finite-dimensional `IsGreatest` or matching growing-m lower theorem is inferred from this source.

# High-dimensional APPT: mathematical review and Lean verification

**Partial formal verification of the overall research. The uniform purity UPPER half is complete; matching lower limits, full extrema, entropy and rigidity theorems are not yet fully Lean-certified.** All physical endpoints use actual complex matrices and the original all-global-unitary APPT definition.

## 1. Completed uniform upper half

For every actual APPT density matrix A on C^m tensor C^n, with 8<=m<=n, Lean proves

    (mn)^2 [purity(A)-1/(mn)]
      <= [m/(m-7)]^2 max{8,4+n/m}.

The final declaration `appt_uniform_asymptotic_upper` proves the quantified consequence: for every real epsilon>0 there is ONE natural M such that the right coefficient can be replaced by `(1+epsilon)*max{8,4+n/m}` for EVERY m>=M, EVERY n>=m, and EVERY APPT density matrix at those dimensions. No fixed aspect ratio is assumed, and states can vary arbitrarily with dimension. A sufficient real threshold for the error comparison is m>=max{8,7+63/epsilon}.

The final physical theorem assumes only dimensions, density and all-unitary APPT. It does not assume a spectral ansatz, graph cap, variance inequality, pivot bound, compactness input or the claimed conclusion. The exact finite predecessor, valid for all 2<=m<=n, is

    purity(A)-1/(mn) <= max{8,4+mn/(m-1)^2} * b^2,
    b=lambda_(mn-m(m+1)/2+1),

where the eigenvalues are canonically ordered and the index is one-based. The generic quantum identity `purity_eq_ordered_eigenvalues` connects the original trace(A*A).re definition to their squared sum.

Six modules assemble and normalize the earlier checked dependencies: `ResidualGraph`, `SpectralBaseline`, `FinitePurity`, `PurityNormalization`, `UniformPurityUpper`, and `AsymptoticUpper`. See `REVIEW_UPPER_ASYMPTOTIC_20261011.md` for the exact proof chain and the three added error controls.

## 1.1 Formalization status at a glance

| Research component | Lean status |
|---|---|
| Actual APPT condition to the finite-dimensional purity upper bound | Verified |
| Connection between physical density-matrix purity and canonically ordered eigenvalues | Verified |
| Explicit dimension-only normalization and upper bound | Verified |
| Uniform asymptotic upper bound for all n >= m as m -> infinity | Verified |
| Matching lower construction for the unrestricted asymptotic maximum | Not yet formalized |
| Joint sufficiency of the three-level counterexample in the Lean development | Not yet formalized |
| Full unrestricted purity maximum, entropy extrema, and rigidity/equality classification | Not yet complete |

## 2. Independent verification

GitHub Actions run **38141972563**, source **87d456235a25114a192c549158723b4f925b416a**, passed every stage. Its fresh review-package Lake build completed **2,837 tasks**, retaining external dependency caches. Physical regressions passed. A trust-zero empty kernel replayed **42,044 transitive declarations and 68 explicit roots**. The only axioms were `propext`, `Classical.choice`, and `Quot.sound`. Replacing only the proof of **`APPTReview.appt_uniform_asymptotic_upper`** by `True.intro`, preserving its type and universe parameters, was rejected.

All **50 pinned local inputs**, including imported quantum definitions and replay support, matched the exact tested commit. Every uploaded proof module, audit, regression, runner and manifest was compared byte-for-byte. The independent kernel log also matches the earlier local WSL kernel log's SHA-256. Source-bound evidence, original logs, roots, complete closure, axioms and artifact metadata are retained in **`verification/ci-87d45623/`**.

The earlier finite-pivot checkpoint independently passed run **38140515745**, source **dcab372f26a250a529112afde26d8cba942d3b32**: 2,834 Lake tasks, 41,998 declarations and 56 roots. Its distinct source-bound evidence is in `verification/ci-dcab372f/`; original local logs remain in `verification/finite-purity-local-20261011/`. No earlier record is relabeled as a later proof.

## 3. Other finite results retained in the audited closure

The package also checks actual arbitrary-eigenvalue witnesses and canonical rank-two consequences, the largest-eigenvalue bound, the necessity of the uniform rank-(mn-1) spectrum for matrix singularity, and the exact sorted nonlinear entropy-head inequality with the paper's pivot. The physical contraction theorem proves that 0<=P<=I implies all-unitary PPT for (m-1)I+2P; projection states of every allowed rank have verified density, APPT and exact purity. Sharp antisymmetric witnesses and real PPT-but-not-APPT density matrices are included as error controls.

The generic triangular graph bounds retain their sign, symmetry and ordering assumptions; the final physical purity theorem proves those conditions rather than supplying them as a surrogate for APPT. The nonlinear entropy-head theorem is still only one dependency of the full entropy law. Earlier independent records remain available under `verification/ci-a3201c67/`, `verification/ci-adcf3348/`, and the other dated checkpoint directories.

## 4. Reproduce

Lean **4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** remain pinned. On Linux or WSL:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

The runner checks source pins and the actual Mathlib checkout, builds the imported review closure rather than the original 879-module qutrit target, compiles replay support with its explicit source root, runs mathematical positive/negative controls and replays all audit roots. Each stage has a finite timeout; on timeout its process group is terminated and literal failure output is retained. `--write-manifest` records an intended source set and does not verify it.

## 5. Remaining obligations and review limits

See `COVERAGE.md`. The newly verified theorem proves only the growing-small-dimension upper half directly for every physical state. It does not yet formalize matching lower graph limits, equality or attainment of a limiting maximum, the complementary fixed-m asymptotic, or exact rectangular optimization and its equality classification. The joint projection-plus-spike sufficiency needed for the three-level counterexample is also still missing. Full entropy minima, rigidity and limiting outlier classifications remain unclosed.

Development caught a real summation-scope mistake, omitted aspect dependence and zero-denominator normalization as potential errors; corresponding exact regression statements are now in the kernel audit. Compilation errors were resolved before the successful CI submissions. A temporary Windows GitHub connection failure was handled by byte-checked transfer to the authorized VPS, and concurrent main updates were merged without overwriting them. No workflow was weakened and no failed proof was counted as verification.

These are independent CI and Lean-kernel checks, not external mathematical peer
review. The old qutrit proof and its immutable release remain unchanged; this
review package does not by itself certify the higher-dimensional analytic
claims in the expanded preprint.
