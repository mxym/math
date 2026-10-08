# Independent replay and proof audit

## What the mathematical proof actually covers

- Consecutive planar conical sectors, with Gaussian measure of
  each cell equal to its angle divided by 2pi.
- Higher-dimensional cylindrical extensions by a Gaussian
  orthogonal factor.
- Angles may equal zero if and only if the floor is zero;
  then empty/null sectors are explicitly permitted.
- Exact global optima and all equality cases stated in paper.md,
  including endpoint and critical mass regimes.

## Detailed proof audit

1. The polar first-moment factor is 1/sqrt(2pi), giving the
   square factor 1/(2pi), with no hidden dimension dependence.
2. The active-face Lagrange equations and full Hessian directions
   reduce every maximum to at most three free equal angles,
   with a separately handled flat two-angle family.
3. A four-quarter-turn critical point is eliminated by an
   explicit strictly improving cubic perturbation.
4. High-mass critical equality is obtained using exact cosine
   superadditivity: two positive excesses have zero merge
   gain, while three positive excesses always admit a
   strictly improving merge.
5. The best global three-sector quadratic constant follows
   from exact defect and variance identities; boundary
   equality proves sharpness and a complete equality list.
6. The first phase transition is unique by a strictly
   decreasing trigonometric phase angle, with derivative
   at most 1-5k/18<0 for all k>=4.
7. The heterogeneous-floor extension uses the same active-face
   stationarity and Hessian directions, with an exceptional
   flat two-angle family pushed to an individual cell's own floor.
   All at-most-three candidate sets are explicitly feasible;
   the result does not assume identical lower masses.
8. The limiting phase constant comes from the exact
   algebraic equation 4c^2+c-2=0 with a simple root,
   giving an O(k^-2) angle error.

## Fixed-mass duality and power-diagram audit

- Weak duality comes from the pointwise maximum of linear
  Gaussian scores with price offsets lambda_i.
- For all positive masses, the price objective is coercive
  after fixing min(lambda_i)=0: it is bounded below by
  p_min times max(lambda_i). It therefore attains its minimum.
- Pairwise distinct score vectors give Gaussian-null affine
  tie sets. Differentiation under expectation is justified
  by pointwise Lipschitzness and dominated convergence.
  Stationarity enforces all prescribed masses exactly.
- Duplicate score vectors are handled by approximation,
  together with uniform Lipschitz continuity of both
  primal and dual objectives in the score vectors.
  No unsupported arbitrary tie-breaking is assumed.
- Euclidean norm duality converts the linear assignment
  problem into a max-min representation of the squared
  centroid objective over finitely many real parameters.
- The final Laguerre structure theorem is conditional
  on a partition attaining the global optimum.
  It proves distinct centroids by swapping equal-mass
  patches and obtaining a strict squared-norm gain.
- Centering all Gaussian score vectors leaves every fixed-mass
  linear objective unchanged. Normalization shows that outer
  maximizers may be taken centered; their span therefore has
  dimension at most k-1.
- The joint law of the centered Gaussian score list depends
  only on its Gram matrix. Orthogonal compression to R^(k-1)
  preserves the entire inner mass-price dual objective.
- Conversely any lower-dimensional feasible partition lifts
  under Gaussian product measure with identical cell masses
  and first-moment score.
- For an attaining partition, the already-proved Laguerre
  structure and the zero sum of centroids force every
  boundary inequality to depend on at most k-1 coordinates.
  This proves cylindrical rigidity without assuming that
  the regular simplex is globally optimal.
- The two-cell all-mass formula is established by a
  sign-definite halfspace exchange, without a solver.
- The three-cell equal-mass global upper bound is
  **attributed to OpenAI-096**, not an independent theorem.
- The fixed-mass outer max-min is still generally
  nonconvex. No claim is made to have proved the full
  Standard Simplex Conjecture.

## High-dimensional counterexample audit

- The score covariance equals the projected iid-Gaussian
  simplex covariance, so E max scores is a scaled normal
  order-statistic expectation.
- Cell symmetry gives equal mass 1/k and collinear first
  moments; this is an identity for the *specific*
  regular-simplex partition, not global optimality.
- Gaussian sign-correlation identity gives the exact
  four-cell tetrahedral objective with arcsin(1/3).
- Uniform all-k strict inequality is split into k=4,
  k=5,6 and k>=7. Each range is supported by one of
  three positive *exact rational* inequalities.
- The log(k) advantage follows from explicit elementary
  upper/lower Gaussian tail bounds; it does not depend
  on heuristic simulations.
- For k=4, the exact floor threshold follows from the
  previously proved planar four-sector closed form.
  Both endpoints of its rational interval bracket
  are independently checked.
- The Gaussian equal-mass *global* simplex optimality
  problem is expressly not claimed to be solved.

## Noise stability and Hermite audit

- Mehler's identity is deduced directly from the standard
  Gaussian exponential generating function, then Parseval
  gives a nonnegative Hermite-level expansion with total
  coefficient mass one for partition indicators.
- The first-degree coefficient is the squared Gaussian
  centroid objective; the zeroth coefficient is 1/k
  for equal-cell partitions.
- The exact four-quadrant full noise stability equals
  [1/2+arcsin(rho)/pi]^2 by independent Gaussian sign
  correlations, not by a truncated numerical model.
- Nonnegative Maclaurin coefficients of arcsine make the
  quotient defining rho_* strictly increasing.
- The tetrahedral high-degree Hermite mass is strictly
  positive because a nonconstant cell indicator cannot
  be a Gaussian-a.e. affine function.
- Rational interval certificates prove both root brackets
  rho_*>29/100 and rho_*<3/10.
- The result compares two explicit partitions, and is
  **not** an all-partition Gaussian simplex theorem.

## Radial universality audit

- Conditional on projected radius, the planar angle is
  uniform; independent radius and direction supply
  exactly the sin(angle/2) moment formula.
- The absence of an atom at zero is needed to interpret
  angle floor as cell-probability floor.
- All transferred comparisons use the same positive
  radial scaling coefficient; equality cases are unchanged.

## Exact-rational code verification

Run python3 check_exact.py from this directory.
The script uses no floating point for proof comparisons:
Machin's identity for pi is enclosed by alternating-series
remainders, every rational conversion is outward-rounded,
every power used in Taylor's series is outward-rounded
to denominator 10^70, and Taylor's theorem bounds the tail.
The final finite-grid sums use exact integer fixed point,
with a rigorously quantified tolerance of 10^-35.
Code checks are independent sanity tests; they are not
used as justification for a universal mathematical claim.
Rational grid cases additionally include unequal cell floors,
and the fully forced boundary sum ell_i=2pi.
The exact tetrahedron-vs-planar score and transition bracket,\nand the positive-noise stability root bracket, are certified\nby outward-rounded arcsine/π intervals.\nSee results/exact-check.txt for passed test list.

## Publication qualifications

Upstream OpenAI-096 proves a general unconstrained inequality
on all measurable Gaussian partitions. This note gives
different *constrained* statements only for planar fan cells.
Do not extrapolate to arbitrary shaped cells. A self-audit
is not external peer review or a historical novelty search.
