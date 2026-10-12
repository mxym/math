# Mathematical provenance and preliminary novelty review

This research note does not claim historical world-first
status, journal acceptance, or independent peer review.
The mathematical methods have significant classical
antecedents and must be compared with coding theory,
Gaussian source coding and Gaussian maxima literature.

## Core classical ingredients

**Primary quantitative Berry–Esseen locator:** I. S. Tyurin,
*A Refinement of the Remainder in the Lyapunov Theorem*,
*Theory of Probability & Its Applications* **56** (2012),
693–696, DOI [10.1137/S0040585X9798572X](https://doi.org/10.1137/S0040585X9798572X).
The journal abstract explicitly states an absolute bound
\(0.5591\) for the **non-identically distributed** summand
case, which rigorously permits our more conservative
constant \(1\). This is a theorem taken from the
literature, not certified by the finite checker.

- **Berry–Esseen inequality** for sums of independent,
  non-identically distributed centered real summands,
  in the standardized form
  sup_x|F(x)-Phi(x)|<=
  C_BE (sum E|X_j|^3)/(sum Var X_j)^(3/2).
  The proof uses the deliberately weak C_BE=1,
  valid under classical published upper bounds.
  For an independently accessible discussion of
  the exact general independent-summand statement,
  see Bo'az Klartag, *A Berry–Esseen type inequality
  for convex bodies with an unconditional basis*,
  referenced at
  https://www.weizmann.ac.il/math/klartag/sites/math.klartag/files/uploads/clt_independent.pdf;
  and standard probability texts (e.g. Petrov,
  *Sums of Independent Random Variables*).
- **Exponential tilting/Cramér change of measure**
  and **conditional Berry–Esseen lower estimates**
  are standard in sharp large-deviation theory.
  We independently derive the exact Rademacher
  log-cosh identities needed for the proof.
- **Binary linear codes over F_2**, pairwise
  independent character evaluations, and
  rank union bounds are classical algebraic
  coding and pseudorandomness tools.
- **Gaussian normal-maximum/quantile comparisons**
  use classical Mills inequalities and Gaussian
  exponential tails, and are proved directly
  with the required constants.
- **Gaussian partition symmetries** and
  source-coding links are related to the
  wider Gaussian noise-stability and rate–
  distortion literature.

## Direct project sources

1. OpenAI Mathematics result family 096,
   *The Gaussian propeller bound in every dimension*.
   Public repository https://github.com/openai/math.
2. Public spherical-cap Gaussian converse:
   https://github.com/mxym/math/tree/main/research/gaussian-spherical-cap-converse.
   Proves necessity Omega((log k)^2) for fixed
   bounded additive error.
3. Public Gaussian dimension-rate theorem:
   https://github.com/mxym/math/tree/main/research/gaussian-centroid-dimension-rate.
   Establishes an O((log k)^3) upper for *all k*.
4. Public arbitrary-mass Gaussian envelope:
   https://github.com/mxym/math/tree/main/research/gaussian-centroid-mass-envelope.
   Supplies the high-dimensional 2/k halfspace
   comparison and full logarithmic asymptotics.

## Scope and originality screening

This manuscript proves the dyadic linear-code
construction and, by **binary-block Gaussian
gluing with uniformly bounded branch entropy**,
extends it to *every* sufficiently large k.
The additive-accuracy dimension therefore has
the optimal growth order Theta((log k)^2)
for all integer cell counts, with an explicit
92/k tolerance.

The gluing step is a rigorously quantified
synthesis of standard entropy coding, product
measure independence and Gaussian centroid
energy additivity. Novelty relative to
Gaussian quantization and group-code literature
requires further specialist examination.

The novelty of this exact formulation and proof
relative to the Gaussian random-linear-code,
spherical compression and sharp rate-distortion
literature remains to be established through a
systematic specialist bibliography search.

## Problems not solved

- Improve sharp dimension and additive constants
  beyond the present Theta(log^2 k) order theorem.
- Explicit efficient construction of binary
  generators meeting the Gaussian maxima objective.
- Improve the absolute additive constant 100,
  or determine optimal dimension constants.
- Exact fixed-k equal-mass Gaussian simplex
  optimality and equality structure.
