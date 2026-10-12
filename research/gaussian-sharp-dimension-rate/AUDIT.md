# Mathematical correctness audit: sharp Gaussian dimension tradeoff

**Review status:** line-by-line internal proof audit. This is NOT
a Lean kernel certificate, independently refereed journal article,
or historical originality claim.

## Exact problem and quantifiers

1. All measurable partitions of standard Gaussian R^d into k
   cells of probability exactly 1/k are allowed. No geometry,
   convexity, regularity or existence of optimal cells is assumed.
2. The asymptotic spherical result is stated only when
   d/(log k)^2 tends to a fixed c in (0,infinity), a regime where
   its displayed spherical-cap asymptotic is uniformly valid.
   The general dimension corollary handles escaping dimensions
   by subsequences, using the prior explicit Omega(log^2 k) bound.
3. The constructive dimension–error curve holds for any fixed
   real A>=1 and every sufficiently large integer k.
   The large cardinality threshold may be extremely large.
   Polynomial-time code generator construction is NOT claimed.

## Normal extreme-value audit

4. Two integrations by parts give
   Phi_bar(t)=phi(t)(1/t-1/t^3+O(t^-5)) with a controlled
   nonnegative remainder <=3phi(t)/t^5.
   Taking q=1/k yields
   t^2=2L-logL-log(4pi)+o(1), h^2=t^2+2+o(1).
5. For independent-normal maximum M_k, normalized variable
   Y=t(M_k-t) converges to standard Gumbel.
   Positive tails have an e^-x envelope. Negative tails are
   bounded in three ranges: [0,t^2/2] by e^-exp(3x/4),
   [t^2/2,t^2] by e^-exp(3t^2/8), and
   [t^2,infinity) by
   t*2^(-(k-1))/sqrt(2pi) after integration.
   These imply uniform integrability, so EY->gamma.
6. The regular simplex has Gaussian scores distributed as
   sqrt(k/(k-1))(Z_i-Zbar). Its symmetry forces each
   cell centroid parallel to its vertex. The exact objective
   is m_k^2/(k-1); the comparison with h_k^2/k
   gives limsup k(U-F_infty)<=2(1-gamma), WITHOUT
   assuming global simplex optimality.

## Spherical-cap asymptotic audit

7. For each equal-mass cell, the Gaussian halfspace bound is
   ||b_i||<=h_k/k. Summing pointwise winning-direction
   scores gives E max_i<u_i,G> >= sum_i||b_i||.
   Therefore kP/h_k <= E max_i<u_i,G> for every
   partition, even if some centroids vanish.
8. Uniform spherical one-coordinate density has
   gamma-ratio constant at most sqrt((d-1)/(2pi)).
   The cap tail after an integration by parts has the
   essential factor [a sqrt(2pi(d-1))]^-1.
   Its log derivative supports a global exponentially
   integrable envelope for the maximum above a.
9. In d~cL^2, choosing
   s^2=2L-logL-log(4pi)-2L^2/d+eta
   gives log(cap union)=-eta/2+o(1). The discarded
   terms are O(L/d+L^2/d^2+L^3/d^2)=o(1).
10. The integrated expected-max ceiling has square
    H^2=s^2+2+o(1), while h_k^2 has the same
    Gaussian -logL-log4pi+2 constants.
    Thus h_k^2-H^2=2L^2/d-eta+o(1).
    The elementary square identity
    h^2-hH >=(h^2-H^2)/2
    yields the precise coefficient 1/c.
11. The global dimension corollary uses BOTH
    k(U-F_infty)<=2(1-gamma)+o(1) and the older
    finite-dimensional lower D_C>=L^2/(C+16)
    to rule out zero-dimensional-ratio subsequences.
    No circular assertion of d~cL^2 is made.

## Tilted binary-code dimension–accuracy audit

12. Every full-rank binary generator defines k=2^r distinct
    Gaussian unit score vectors, permuted transitively by a
    diagonal orthogonal sign-flip group. The argmax cells have
    exactly equal Gaussian measure 1/k.
13. For a fixed Gaussian coefficient vector, two distinct
    nonzero binary messages evaluate to pairwise independent
    Rademacher score vectors over the independent uniformly
    sampled generator columns. Chebyshev on the exceedance
    count needs only pairwise independence, not mutual
    independence among all messages.
14. On good Gaussian coefficients Q2 in [1/2,2], Q4<=10/m,
    the tilted Rademacher sum has variance V in [1/4,2].
    Its third absolute moment total is at most
    8sqrt(Q2Q4)<=8sqrt(20/m).
15. We use the published Berry–Esseen theorem for *independent
    nonidentically distributed* summands with deliberately
    nonoptimal absolute constant 1. This gives CDF error
    <=64sqrt(20/m)<288/sqrt m.
    At L>=1e10 and m>=L^2, the doubled error is strictly
    below 1/(20lambda), leaving a positive local tilted
    probability bound.
16. The improved cutoff B=(log L)/2+6 is <=lambda/4.
    The Cramer change of measure and the exact inequality
    Lambda-lambda*mu>=-L establish a weighted-Rademacher
    tail probability, while pairwise Chebyshev gives
    P_g(M<s_y|G)<=80e^-5 e^-y, with
    80e^-5<3/5 by rational exponential inequalities.
17. Integrating the y-dependent failure gives expected
    maximum loss eta/lambda, not an unjustified
    constant loss based on one tail point. The deepest
    tail uses M>=X0 and lambda>=sqrt L.
    The exponential remainder is <1/(10sqrt L)
    at L>=1e10.
18. The Gaussian weight fluctuation error is
    7/(sqrt A sqrt L), the fourth-moment error
    8/(A sqrt L), and the bad-good-event Gaussian
    contribution <=1/(sqrt A sqrt L). The
    dimension-independent terms sum strictly below
    5/sqrt L because 6/sqrt2<17/4,
    80e^-5<3/5 and the exponential remainder is <1/10.
19. The generator rank-failure probability is <=
    exp(L-(2/3)A L^2)<=1/(A L^2) for L>=1e10,A>=1.
    Every fixed-generator Gaussian maximum has second
    moment <=2L+3. Cauchy–Schwarz then costs at most
    2/(sqrt A sqrt L) to restrict to full-rank
    generators. The total loss becomes
    T_A=5+10/sqrt A+8/A.
20. Square the expected score bound only after verifying its
    right side positive for L>=1e10. The Gaussian
    normal-quantile ceiling h_k^2<=2L-logL+3 and the
    unit-score Cauchy–Schwarz inequality imply the
    exact local gap (3+2sqrt2*T_A)/k.

## All-integer Gaussian selector

21. Decreasing distinct binary powers obey
    S_(j+1)<w_j and S_j<=2^(1-j).
    The exact chain formula
    H(w)=sum_j S_j h_2(w_j/S_j)
    yields H(w)<2log2; k=2^s-1 approaches equality.
22. One independent Gaussian selector chooses dyadic block
    j with probability q_j/k. A common Gaussian data block
    implements exactly q_j equal-mass cells; all final
    cells have mass exactly 1/k, even when k has many
    binary digits or includes a singleton block.
23. The full squared data-coordinate first moments contribute
    sum_j(q_j/k)^2 P_j. Dropping selector-coordinate
    squared moments is a valid nonnegative relaxation.
24. The globally 2-Lipschitz squared Gaussian upper hazard
    bounds the binary split's lost halfspace energy by
    2H(w)<4log2. Small blocks below fixed Q0 have total
    mass below Q0/k and loss <=2Q0 logk/k<1 for
    k>=Q0^2. Thus the exact all-k loss budget
    is 4+4log2+2sqrt2*T_A.
25. Seven table points are certified with the rational
    upper bounds log2<7/10 and sqrt2<99/70.
    Negative controls verify that binary sorting and
    strict accuracy comparisons have not been dropped.

## Exact computer evidence and limitations

The checker is Python 3 standard library only. All
finite-parameter comparisons use exact Fraction arithmetic,
pi via an alternating arctangent formula, logarithms via a
positive arctanh series, and explicitly outward-rounded
fixed-point integer intervals. Its nine spherical-cap
cases include k as large as 10^1000.
Rational tests also cover seven (A,C) pairs and fifteen
binary mass distributions.

These tests **do not prove** uniform integrability
or the Berry–Esseen theorem. Both mathematical arguments
are explicitly established or cited, with full hypotheses,
in paper.md. The checker is supplementary validation,
not a universal proof engine.

## Remaining gaps

- Sharp leading coefficient of D_C(k)/(log k)^2 and
  whether the limit exists.
- Best achievable additive-error constant as the
  dimension coefficient A grows.
- Effective construction of high-quality binary generators.
- High-dimensional global simplex optimality for fixed k>=4.
- Independent specialist novelty review and Lean formalization.

Do not describe any of these as solved by this note.
