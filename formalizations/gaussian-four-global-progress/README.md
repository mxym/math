# Four balanced Gaussian cells — partial Lean formalization / 部分形式化

**Unconditional partial results, not the global sharp theorem.** The inequality
with constant `12 * (arctan (sqrt 2))^2 / pi^3` and its complete equality
classification are not proved or exported by this package. No missing
geometric theorem is assumed as a custom axiom. No completion Release or DOI
is created for this checkpoint.

## Current verified checkpoint

The 90-module source set at `dce885e1e91f6b647cf5327dad6bb1b25ebee2f6`
passed fresh local verification and independent GitHub-hosted verification:
[run 38065291099](https://github.com/mxym/math/actions/runs/38065291099).
The earlier repaired 89-module source set passed
[run 38064502958](https://github.com/mxym/math/actions/runs/38064502958).

| Check | Current 90-module result |
| --- | --- |
| New Lake source tree, initially zero owned objects | PASS |
| Separate source compilation into a second empty object directory | All 90 modules PASS |
| Declared audit roots | 547 |
| Empty-kernel replay | 60,487 declarations, trust level 0 |
| Axioms | Only `propext`, `Classical.choice`, `Quot.sound` |
| Deliberately false Lean source mutations | All 9 REJECTED |
| Module/import/audit inventory regression tests | All 5 PASS |
| Local versus independent CI | All source hashes and 90 object hashes identical; replay and mutation results identical |

These are counts of a partial proof's audited dependency closure, not a claim
that 60,487 separate Gaussian theorems have been proved. Historical 31-module
receipts and failed development checkpoints do not verify the current source.

Literal local logs, failed mutation sources, dependency checks, source/object
SHA-256 values and replay closure are in
`evidence/ci-repair/local-90/complete-logs.tar.gz`. The original unmodified
Actions artifact is `evidence/ci-repair/ci-90/original-actions-artifact.zip`.
`evidence/ci-repair/COMPARISON.json` records cross-host equality checks.
The historical failures and their successful successors are documented in
[CI_REPAIR.md](CI_REPAIR.md), with original-artifact hashes and retained literal
diagnostic logs. Proof failures have not been suppressed or ignored.

## Newly verified mathematical coverage

### Actual price Frechet Hessian and centered invertibility

For affine-independent k inducing scores in R^(k-1), the development uses
actual Gaussian winning sets and the original integral price objective. It
proves the genuine second Frechet derivative, not just a directional formula.
One constructed positive symmetric Gaussian flux family supplies the actual
Bochner flux, cell-mass derivative and price Hessian. Its quadratic form is

    q^T L q = (1/2) sum_(i,j) w_ij (q_i-q_j)^2.

Its exact kernel is the constant-price shifts. `CenteredPriceHessian.lean`
constructs the submodule H={q : sum_i q_i=0}, proves that L maps H into H,
proves strict positivity on nonzero H, and proves the restricted linear map
is bijective. In the four-cell case the score space here is the intrinsic
R^3. Degenerate diagrams are not silently included.

Main new entry points:

```lean
GaussianFour.actual_simplicial_price_hessian
GaussianFour.actual_simplicial_price_hessian_nondegenerate
GaussianFour.centeredPriceHessianMap_bijective
```

See [HESSIAN_PROGRESS.md](HESSIAN_PROGRESS.md). Price-Hessian invertibility
does not by itself prove its joint-parameter continuity, the smooth implicit
price map, or the separate covariance Hessian needed by the global argument.

### Actual covariance differential and full-rank local criticality

The integrated `analytic/` sources construct the actual covariance value,
its Gaussian interpretation, factorization invariance, PSD-cone continuity
and scaling. `FixedCovarianceDifferential.lean` constructs a fixed actual
Gaussian flux family before quantifying over centered covariance directions:

    derivative at zero of t -> C(Q+tD) = trace(L D)/2.

This is a directional statement, not a claimed full covariance regularity
result. `CovarianceCriticality` and `SelfMomentCriticality` use it at a
full-rank constrained local extremum to prove C(Q)>0, actual winning masses
1/4, actual Bochner moments m_i=C(Q)r_i, and L=C(Q)P.

```lean
GaussianFour.actual_centered_covariance_fixed_differential
GaussianFour.actual_four_local_extremum_self_moments
```

These theorems do not classify the local extrema or prove the missing sharp
global comparison. The exact remaining statements are in [GAPS.md](GAPS.md).

### Retained analytic and spectral core

The earlier checked modules prove actual fractional pair-moment separation,
four-cell non-coalescence, a positive-mass triple-tie obstruction, exact
quarter-quantile margins and quartile moments, and the ordered collinear
self-moment spectral obstruction with actual Gaussian projection/Bochner
transport. They also prove actual balanced price bounds and compactness,
all-matrix upper-normal equivalence with complementary slackness, and the
intrinsic three-dimensional regularization residual identity and estimate.

The sibling actual-measure/price sources and six mass-envelope analytic
sources are reused by source path. Integrated research-branch source provenance
is recorded in `UPSTREAM_PROVENANCE.json`; no branch-local theorem counts
merely because an old log or manuscript says it is proved.

## Reproduction

Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** and all transitive
dependencies are locked by `lake-manifest.json`. The verifier checks dependency
Git revisions and LF-normalized source blobs, as well as owned source hashes.

With the pinned Lean toolchain on PATH:

```bash
cd formalizations/gaussian-four-global-progress
python3 preflight.py
python3 test_preflight.py
bash fetch_cache.sh
python3 reproduce.py --output-dir /tmp/gaussian-four-independent-check
```

The output directory must not already exist. An existing checked dependency
cache may be supplied explicitly with `--mathlib-dir`; no existing owned
object is reused by the fresh proof verification. `GaussianFour.lean` is the
aggregate entry of this **partial** package, not a main theorem asserting the
sharp four-cell inequality.

`MODULES.json`, `ROOTS.txt`, `SOURCE_BLOBS.json`, `audit/Audit.lean` and
`audit/Replay.lean` specify the exact checked inputs and declarations.
`DEPENDENCY_GRAPH.dot` is generated from their owned imports;
`DEPENDENCY_MAP.md` maps manuscript obligations to the checked Lean statements.
The replay rejects unexpected axioms, unsafe/partial mathematical dependencies,
and mismatching original/replayed theorem types or universe parameters.

Nine mutation controls cover the quartile bound, boundary and moment signs,
price bound, normal-cone sign, residual bound, covariance factor 1/2, price
Hessian kernel, and centered Hessian curvature sign. They must fail actual
Lean compilation for a proof reason. They are not numerical tests of the
Gaussian theorem and are not a replacement for any missing analytic proof.

## Remaining global scope

The missing blocks include higher covariance regularity, the actual
covariance Hessian and tetrahedral local maximum, singular facet convergence,
the constrained deformation/mountain-pass argument, complete rank-two and
arbitrary rank-one boundary reductions, actual Gaussian perimeter lower
bounds, the exact tetrahedral arctangent evaluation, and the final arbitrary
measurable/fractional inequality with both directions of the AE geometric
equality classification. These are substantive mathematical gaps, not a
final packaging step. See GAPS.md for the precise obligations.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding; AI-assisted research.
Existing licenses and third-party notices are preserved. Original additions
retain all rights not otherwise granted. No external peer-review or priority
claim is made. Existing immutable editions remain unchanged.
