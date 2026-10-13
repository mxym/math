# Four balanced Gaussian cells — partial Lean formalization

**The sharp global inequality and its complete equality classification are
NOT proved by this package. No completion Release or DOI is created.**
All exported mathematical results are unconditional under their stated
object-level hypotheses. No missing geometric theorem is inserted as an
axiom or hidden premise of a purported sharp theorem.

## Current analytic progress

The newest extension proves actual competitor-price derivatives at arbitrary
positive-mass Gaussian winning diagrams without affine independence. It
identifies intrinsic facet coefficients with every positive orthogonal chart,
proves their joint continuity, and passes the actual Bochner moment flux and
entire Laplacian matrix to distinct-score limits of balanced simplicial
diagrams. Eight new modules and one byte-identical reused source are integrated.
See [INTRINSIC_BOUNDARY_PROGRESS.md](INTRINSIC_BOUNDARY_PROGRESS.md) and [THEOREM_MAP.md](THEOREM_MAP.md).

Principal entries:

```lean
GaussianFour.actual_competitor_price_derivative
GaussianFour.positive_pair_charts_compatible
GaussianFour.continuousAt_intrinsicPairWeight
GaussianFour.balanced_simplicial_limit_laplacian
```

These concern actual standard Gaussian measures, measurable winning cells,
and Bochner integrals. The limiting theorem explicitly requires converging
scores/prices, affine-independent approximants, prescribed positive masses,
and distinct limiting scores. It proves, rather than assumes, the limiting
masses, moment flux identity and coefficient convergence. For four cells in
intrinsic R^3, instantiate its dimension parameter d=2.

The retained development includes Gaussian fractional partitions, balancing
prices, primal-dual equality, covariance value and directional derivatives,
full-rank critical self-moments, the actual price Hessian and centered
nondegeneracy, moment separation, quartile/rank-one analysis, arbitrary-label rank-one representation and winning-cell transport, rank-two affine-dependence and sign-structure extraction, normal cones,
regularization residuals and fixed facet-chart continuity. Price Hessians
are not covariance Hessians; no such identification is claimed.

## Verification and reproduction

Toolchain: Lean 4.34.1, commit
5045d0056413266e57c625dcd7c365b10e377c52.
Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612.
All transitive versions are fixed in lake-manifest.json. The current inventory
has 109 modules and 641 audit roots. Fresh reproduction `repro-20261013-hull` passed after the rank-two convex-hull/sign additions; its receipt is in `evidence/repro-20261013-hull/`. The earlier sign receipts are retained as historical evidence.

```bash
cd formalizations/gaussian-four-global-progress
bash fetch_cache.sh
python3 preflight.py
python3 test_preflight.py
python3 reproduce.py --output-dir /tmp/gaussian-four-independent-check
```

The output directory must be new. The reproducer reconstructs a fresh Lake
source tree with zero owned objects, builds it, separately compiles all owned
modules into a second empty object directory, audits every listed root, and
replays the used declaration closure into mkEmptyEnvironment 0. Only propext,
Classical.choice and Quot.sound are allowed. Sources are checked before and
after. Thirteen deliberately wrong source mutations must be rejected by Lean,
including the new derivative sign and chart-coefficient normalization tests.

MODULES.json fixes the build order; ROOTS.txt and audit/ fix verification
roots; SOURCE_BLOBS.json binds reproduction inputs. DEPENDENCY_GRAPH.dot and
DEPENDENCY_MAP.md give the proof dependencies. BOUNDARY_PROVENANCE.json binds
source reuse. GaussianFour.lean is the aggregate entry for these partial
results, not an entry to an already completed sharp global theorem.

## CI failures and exact remaining gaps

[CI_REPAIR.md](CI_REPAIR.md) records the real source errors behind historical
failed runs and their successful successor checks. The preflight detects
unlisted modules, bad import order and audit-root drift. Failed proof steps
are never disabled; the full expanded check must succeed before publication.

[GAPS.md](GAPS.md) lists the missing covariance higher regularity/Hessian,
variational deformation and critical sequence, remaining spectral transport,
rank-one extraction and complete rank-two exclusion, actual Gaussian
perimeter lower bounds and multi-bubble input, exact tetrahedral arctangent
evaluation, sharp covariance comparison, and final measurable/fractional
equality classification. These are mathematical obligations, not packaging.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. mxymmxym1@gmail.com.
ORCID 0009-0000-3864-3536. No external funding; AI-assisted research.
Existing licenses and third-party notices remain in force. Original additions
retain all rights not otherwise granted. No external peer review is claimed.
