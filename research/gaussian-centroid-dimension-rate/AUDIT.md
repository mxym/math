# Proof fidelity and exact replay audit

## Checked hypotheses

- Measurable *ordered* partitions of standard Gaussian space,
  exactly k cells of mass 1/k, with arbitrary cell geometry.
- Real dimension d, not finite alphabet or finite grid.
- Statements about arbitrary masses are explicitly restricted
  to the rate-distortion **upper bound**, not the b-ary
  constructive lower bound.
- The b-ary construction is exact for all integers k>=2,
  with a universal analytic node-energy lower bound that
  is informative for sufficiently large b.
- The separate large-k threshold K_epsilon is explicit
  and may be very large. No computational efficiency
  of evaluating inverse normal CDF to machine tolerance
  is assumed in the mathematical construction.

## Independent proof-structure review

1. The analytic normal-hazard lower bound uses exact
   Gaussian Mills inequalities for q<=1/10; for q>1/10
   the claimed lower bound is negative, proved via
   elementary bounds e>27/10, pi<22/7 and log2>2/3.
   Its coefficient -4 is explicit.
2. The residual entropy inequality
   sum q_j log(1/R_j)<=1 does **not** need sorting,
   because log(1/s) is decreasing in s and the
   probability intervals telescope.
3. Balanced integer recursion produces at any regular
   node b nonempty children of probabilities between
   1/(2b) and 2/b. Each level before the last has
   only b-way nodes; exact integer induction checks
   the global leaf-count balance.
4. The same Gaussian block is shared by all nodes at
   the same level, which is legitimate because their
   earlier-coordinate events are disjoint. Branch
   thresholds depend only on earlier node labels.
5. Conditional mean of a final leaf is the orthogonal
   concatenation of its levelwise conditional means.
   This is proved by independent Gaussian coordinate
   blocks, not by assuming arbitrary conditional
   independence within one block.
6. Every b-way node's mean-square conditional energy
   is at least 2 log(b/2)-log log(2b)-6.
   The proof includes the last child, whose dedicated
   coordinate is absent, by defining h(1)=0 and
   using only a nonnegative lower bound.
7. At each of the first T-1 levels, the reaching-node
   probabilities sum to 1, so each contributes L_b/k
   to the final squared first-moment objective.
8. The ambient dimension is (b-1)T. Choice of b
   comes from a proven limit L_b/(2logb)->1;
   choice k>=b^{ceil(2/epsilon)} makes the other
   ratio factor >=1-epsilon/2. Their product exceeds
   1-epsilon.
9. The rate-distortion converse is obtained from
   conditional Gaussian maximum entropy, Jensen,
   I(X;Y)=H(Y), and the conditional-variance
   orthogonal decomposition. Covariances are
   positive definite for positive Gaussian-mass
   cells; no entropy formula is used on a
   singular conditional distribution.
10. The dimension-rate curve f(c) is strictly
    increasing. Its inverse gives a necessary
    relative dimension coefficient c_epsilon.
    This is different from claiming an exact
    optimal dimension coefficient.
11. For additive O(1/k) accuracy, the
    rate-distortion gap is
    d(x-1+e^{-x}), x=2logk/d.
    The high-dimension optimum
    2logk-loglogk+O(1), multiplied by 1/k,
    forces x->0 and yields the rigorous
    necessary lower coefficient 2.
12. The exact regular-simplex block-product objective
    is computed by matching score covariance matrices,
    simplex symmetry and independence across blocks.
13. The equal-mass one-pass staircase exact
    coefficient identity is independently obtained
    from diagonal and off-diagonal Gaussian moments.
    The additive asymptotic loss 2/k follows from
    a dominated logarithmic Riemann sum and a
    negligible O((logk)^2/k) tail.

## Exact arithmetic controls

The checker verifies several **nontrivial proof interfaces**:

- All children of every enumerated b-ary node have
  positive **integer counts** summing to their parent.
- Their conditional Gaussian masses can be assigned
  exactly, because parent probability m/k times
  child ratio n/m is exactly n/k in rational arithmetic.
- Every regular node's child ratio lies between
  1/(2b) and 2/b, and all early levels contain
  only regular nodes.
- Explicit integer arities b=10^10, 10^30, 10^60,
  and 10^140 satisfy the chosen rigorous sufficient
  inequalities for four fixed tolerances.
- Logs of rationals use the positive arctanh series
  and **outward** fixed-point rounding at denominator
  10^85, including the geometric tail.
- The root-bracket controls on the Gaussian
  rate-distortion curve use rational exponential
  series with rigorously signed remainders.
- No floating point or stochastic optimizer is
  used in any certified comparison.

The universal Gaussian calculus, maximal differential
entropy, and limit theorems are proved *in the
manuscript* rather than inferred from finite checks.

## Open mathematical questions

- The optimal constant factor C_epsilon in
  d=C_epsilon log k, especially as epsilon->0.
- A constructive dimension upper bound matching
  the necessary scale (logk)^2/loglogk for
  additive O(1/k) precision.
- Sharp dimension-dependent results for arbitrary
  unequal mass vectors, where collision entropy
  and Shannon entropy may compete.
- Whether random spherical codebooks or correlated
  Gaussian rate-distortion constructions improve
  the explicit balanced-threshold constants.

No world-first or independent-peer-review claim
is made in this self-audit.
