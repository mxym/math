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
7. The limiting phase constant comes from the exact
   algebraic equation 4c^2+c-2=0 with a simple root,
   giving an O(k^-2) angle error.

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
See results/exact-check.txt for passed test list.

## Publication qualifications

Upstream OpenAI-096 proves a general unconstrained inequality
on all measurable Gaussian partitions. This note gives
different *constrained* statements only for planar fan cells.
Do not extrapolate to arbitrary shaped cells. A self-audit
is not external peer review or a historical novelty search.
