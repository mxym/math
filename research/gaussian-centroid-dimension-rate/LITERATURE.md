# Literature and attribution screening

**No mathematical priority or world's-first claim.**
This screen is preliminary, focused on differentiating
well-known Gaussian rate–distortion tools from
the exact balanced-threshold claims proved here.

1. OpenAI Mathematics 096, *The Gaussian Propeller Bound in
   Every Dimension*, 24 September 2026:
   https://github.com/openai/math.
   Establishes the unconstrained Gaussian first-moment
   maximum, and motivates the fixed-mass program.
2. Our arbitrary-mass Gaussian centroid envelope:
   https://github.com/mxym/math/tree/main/research/gaussian-centroid-mass-envelope.
   Proves a global additive 2 sum_i p_i^2 bound to the
   individual halfspace ceiling. In the equal-mass
   case it gives the high-dimensional optimum
   2logk-loglogk+O(1) over k.
3. Our Gaussian propeller/fixed-mass duality research:
   https://github.com/mxym/math/tree/main/research/gaussian-propeller-balanced-fans.
   Supplies dimension stabilization at k-1 for
   the exact fixed-mass Gaussian first-moment problem.
4. Claude Shannon, Gaussian rate–distortion theory;
   Thomas Cover and Joy Thomas, *Elements of Information
   Theory*, rate–distortion chapter. The Gaussian
   conditional-entropy lower bound is classical and
   is used here as a fully derived **converse**.
5. Anindya De, Elchanan Mossel, Joe Neeman,
   *Noise Stability is Computable and Approximately
   Low-Dimensional*, Theory of Computing 15 (2019),
   Article 6, https://www.theoryofcomputing.org/articles/v015a006/.
   This work has a different optimization objective
   (full Gaussian noise stability), using additive
   approximation with dimension bounds.
6. Badih Ghazi, Pritish Kamath, Prasad Raghavendra,
   *Dimension Reduction for Polynomials over Gaussian
   Space and Applications*, arXiv:1708.03808.
   Different low-degree Gaussian dimension reduction
   setting; relevant to possible extension strategies.
7. Classical Gaussian vector quantization literature
   and fixed-rate quantizers:
   the centroid score is related to mean-square
   Gaussian quantization distortion and its
   rate-dependent dimension behavior.
   Historical novelty of the dimension scaling,
   viewed under this correspondence, has not yet
   been determined.

## Additional cyclic-orbit construction

The present note also uses deterministic orbits of cyclic
orthogonal group actions, epsilon-biased trigonometric
frequencies and Gaussian comparison via log-sum-exp
covariance interpolation. All are established methods
in harmonic analysis, pseudorandomness and Gaussian
process theory (Slepian and Sudakov–Fernique inequalities).

Their synthesis here constructs **exactly equal-mass**
Gaussian score cells in O((log k)^3) dimensions and
proves an explicit additive 14/k approximation to
the unrestricted high-dimensional centroid optimum.
It should be compared with spherical coding,
small-bias sets, and Gaussian vector quantization
before any independent originality claim.

## Distinct mathematical statements proved in this note

- A *deterministic, all-k* balanced Gaussian threshold
  tree with dimension O_epsilon(logk), exact equal
  masses, and a rigorously quantified fraction
  of the fully unrestricted squared-centroid optimum.
- An explicit b-way normal-quantile energy lemma
  with elementary logarithmic lower bound,
  valid for nonuniform balanced child proportions.
- A precise rate-distortion converse giving an
  exact dimension-dependent squared-centroid
  upper bound and the optimal logarithmic
  **order** of relative dimension saturation.
- The necessary dimension scale
  (2-o(1))(logk)^2/loglogk for preserving the
  high-dimensional **second logarithmic term**.
- A cyclic almost-orthogonal score orbit yielding
  an exact equal-mass additive 14/k approximation
  in at most 8(log k)^3+2 Gaussian dimensions.
- An exact b-ary regular-simplex product identity
  for k=b^t.
- A mathematically exact method-level asymptotic
  loss 2/k for the earlier one-pass staircase,
  identifying a limitation of that construction.

These theorems have complete demonstrations in
paper.md and rational proof-interface tests.
Not all the constituent concepts are new; the
historical status of the combined claims requires
additional specialist screening before journal
submission. In particular the rate–distortion
converse is not claimed to be a new inequality
in information theory.

## Open problem

Our upper and lower dimension orders match for
fixed relative epsilon, but the minimal dimension
for **additive O(1/k)** precision now lies
between the proved necessary scale
(2-o(1))(logk)^2/loglogk and the explicit
sufficient 8(logk)^3+2. Closing this
polylogarithmic gap is the next high-value problem.
