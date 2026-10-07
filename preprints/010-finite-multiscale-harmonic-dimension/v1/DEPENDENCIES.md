# 010 v1 dependency map

## Pinned upstream source

Repository: openai/math

Pinned commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a

Result family: 361 — Failure of integer-degree harmonic dimension comparison.

Primary source directory:

preprints/A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/build/sections/

The present manuscript does not reprove the long analytic construction in
family 361. It proves a finite-multiscale angular assembly statement and
checks that the published analytic machinery requires only the resulting
finite-program properties.

## Exact imported ingredients

### crossings.tex

- n:lem-two-directions: at an exact two-dimensional eigenspace there are
  conformal directions realizing the needed traceless first-order matrix
  directions. We use its off-diagonal consequence at each crossing.
- n:lem-avoidance: simplicity through any fixed finite cutoff is dense, and
  simple endpoints can be joined by a smooth path remaining simple through
  that cutoff.
- n:lem-retained-double: a chosen exact isolated double can be retained while
  every other multiplicity through any larger finite cutoff q is split,
  including a strict gap after q; the perturbation can be arbitrarily small.
- n:lem-adjacent-doubles: for the one-scale band B_L+1,...,B_M, every
  adjacent pair can be realized as an isolated exact double inside any
  prescribed sufficiently small neighborhood.

The multiscale proof applies n:lem-retained-double with the largest cutoff
p_m+1 to doubles originally produced for each individual band. This is the
key common-cutoff step.

### angular-program.tex

- n:prop-angular-program: one-band adjacent-swap loop, eigenline
  continuation, return-cycle calculation, and rank-average estimate.
- n:eq-near-round-frequency-bound: uniform ordered eigenvalue bound in a
  sufficiently small angular neighborhood.
- n:eq-band-frequency-average: exact one-band rank-average bound.

The 010 manuscript redoes the permutation and averaging step for several
pairwise disjoint bands. It does not import a multiband theorem.

### geometry.tex

- n:prop-radial-realization: uniform Ricci-nonnegative radial realization for
  a fixed finite angular program and all crossing-control sequences.
- n:eq-global-tensor-comparison: global comparison to the Euclidean metric.
- n:geometric-consequences: asymptotic volume ratio, tangent-cone
  description, and radial sectional-curvature consequence.

The proof of n:prop-radial-realization uses finite smooth bounds of the fixed
angular program; it does not use that the return permutation has only one
nontrivial cycle.

### transfer.tex

- n:lem-inward-transfer: exact whole-ball restriction maps and frozen
  comparisons.
- n:prop-exact-graphs: invariant graph over the first p angular modes.
- n:prop-outward-crossing: signed first-order off-diagonal response to a
  crossing control.

The source explicitly allows constants to depend on the fixed finite
program and on p; uniformity as the degree grows is not required. It is
uniform over all controls once that finite program is fixed.

### matching.tex

- n:lem-matching-weights: stable propagation and endpoint sign control for
  each pair.
- Section Simultaneous matching: all crossing controls and line coordinates
  are selected by finite-dimensional Brouwer approximations followed by a
  coordinatewise diagonal limit.
- n:eq-exact-lines: exact invariance of every selected continued line.

The argument distinguishes only two possibilities for a pair of continued
labels: isolated recurring simple crossings with bounded phase gaps, or a
uniform gap. In the 010 program, labels in one band satisfy the first case
over the common finite period, while labels in different bands satisfy the
second.

### growth.tex

- n:eq-mesh-exponent: each matched line has exact logarithmic spherical
  growth exponent equal to its periodic mean cone frequency.
- n:eq-all-radius-sphere-bound: exact inward contraction controls every
  intermediate radius.
- Section Entire harmonic functions and growth at every radius: compatible
  whole-ball traces give independent entire harmonic functions, and local
  elliptic estimates convert a strict mean-frequency margin into the
  pointwise polynomial-growth condition.

For 010, the exact exponent statement is applied separately to each finite
prefix 1,...,p_r, whose maximum mean is strictly below k_r.

## Non-imported steps proved in 010

1. Recursive selection of disjoint spectral bands at arbitrarily separated
   integer scales.
2. Promotion of each individual-band double to one common largest cutoff.
3. Construction of one finite loop whose return permutation is a product of
   disjoint cycles.
4. Introduction of a common period Q S, where Q=lcm(N_1,...,N_m).
5. Exact rank-average identity for every band in the presence of all other
   band loops.
6. Prefix mean-frequency bound max_{i<=p_r} mu_i < k_r simultaneously for
   all selected scales.
7. Conversion of those prefix bounds into simultaneous dimension failures
   on m consecutive integer-degree blocks.

## Scope

This dependency map is pinned to a commit. If the upstream proof changes,
the imported claims should be re-audited before updating the pin.

No claim of literature novelty or priority is made.
