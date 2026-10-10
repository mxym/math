# Audit and verification scope

8 October 2026. This package contains a complete traditional mathematical
proof. It does not claim external mathematician review, a whole-proof Lean
formalization, or independently confirmed worldwide priority.

## Mathematical endpoint

Four prescribed equal Gaussian cell masses, every dimension d≥3, arbitrary
measurable and fractional partitions, the sharp squared first-moment value,
and all equality cases. The manuscript does not depend on numerical searches.
Its source/statement comparison is in `LITERATURE_STATUS.md`.

The proof's global chain is:

1. A smooth covariance value function has gradient L/2 in the positive cone.
2. Full-rank trace-constrained criticality forces L=μP. The established
   multi-bubble perimeter theorem then puts its value at least c*.
3. The regular covariance is a strict local maximum of value c*.
4. Any additional point of value at least c* forces a lower-valued critical
   point for the smooth regularization, by a completely proved constrained
   projection-flow mountain-pass lemma.
5. The upper normal cone supplies L≤μP and the top-eigenspace relation.
   Its exact residual bound and the winning-cell median inequality keep
   all score pairs uniformly separated in the zero-regularization limit.
6. Prices and facets converge. At a singular limit, self-moment rank-two
   and rank-one obstructions contradict L≤P. At a nonsingular limit the
   critical-value perimeter lower bound contradicts its lower barrier value.
7. The covariance inequality returns to all partitions by the feasible
   assignment inequality, with equality forced by distinct regular scores.

The critical-value perimeter bound alone is not a global upper bound;
the boundary/deformation steps are essential. The argument does not require
full covariance concavity. Codimension-one triple ties are excluded using
all four positive masses, rather than being silently ignored.

## Imported results

Classical single-cell Gaussian isoperimetry [Borell; Sudakov–Tsirelson] and
Milman–Neeman's Annals 2022 Gaussian multi-bubble theorem are imported.
The latter applies to four cells in dimension three and to total interface
area, one half the sum of individual perimeters. Equal masses make its
regular Voronoi minimizer central by symmetry and unique balancing prices.
The three-cell bound, exact profile estimate, local Hessian and deformation
lemma are proved inside this paper. Gaussian integration by parts and the
usual finite-dimensional spectral/implicit-function/ODE theorems are used
explicitly. Partial Lean does not replace any imported analytic result.

## Reviews and arithmetic

Two separately tasked research agents reviewed the complete proof and the
final manuscript. Their records include source hashes, concrete derivations,
boundary cases and limitations in `review/`. These are internal model reviews.

`check_exact.py` uses only rational arithmetic. Its finite fixed matrix grids
check normal-cone/residual normalizations, including non-diagonal matrices
in a top eigenspace. It checks the local polynomial Hessian identity and
Taylor margin, and detects an omitted-KKT variant and a weakened-profile
variant. Running with Python optimization yields identical output; checks
use explicit failures rather than disabled `assert` statements. The finite
checks are not an analytic proof certificate.

Eight Lean exports are freshly compiled and their full used declaration
closure is replayed in an empty trust-level-zero kernel. The intentionally
false source must fail; its actual rational countermodel is also checked by
Python. `results/lean.json` binds logs, sources, compiler hash and package
revision checks. The 7,286 declarations are a partial algebra closure, not
a count of formalized analytic endpoint declarations.

`verify.py` reruns exact controls, validates package hashes, compares normal
and optimized output, and verifies the recorded partial Lean provenance.
It does not silently perform a fresh Lean build. The separate replay command
in `formal/README.md` does. The PDF has eleven pages and editable sources.
PDF metadata is fixed by `build.py`; disclosure timestamps come from the
public commit and verified immutable release, not the PDF's date string.

## Lean core extension (development, 2026-10-10)

The checked partial package now proves equation (10) from actual Gaussian
winning masses and gives centered-price subsequential compactness. It also
proves the universal PSD trace-one upper-normal equivalence and the intrinsic
three-dimensional regularization residual identity and estimate behind
(20)-(21). See `formalizations/gaussian-four-global-progress/CORE_PROGRESS.md`
for exact Lean types and the explicit remaining coordinate/analytic bridges.
The used closure has 31 modules and 222 audit roots; the new source-bound
local report is `evidence/core-r1/verification.json` in that package.

These results do not formalize the actual Gaussian facet convergence,
mountain-pass construction, geometric perimeter inputs, or sharp equality
classification. The global theorem is still only partially formalized.
No complete-formalization or external-peer-review claim is justified by this
core extension, and no immutable manuscript release has been modified.
