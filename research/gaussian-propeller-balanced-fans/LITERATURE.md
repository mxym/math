# Focused literature and novelty assessment (8 October 2026)

This is a **non-exhaustive** first bibliographic screen. The note
does **not** make priority or worldwide originality claims. Every
theorem in paper.md is accompanied by a complete analytic proof
(or, for explicitly attributed global comparator statements, an
identified published source).

## Direct source and exact comparator

- **OpenAI Mathematics, result family 096**, *The Gaussian propeller
  bound in every dimension*, 24 September 2026.
  Pinned source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf
  This establishes the unconstrained maximum of squared Gaussian
  first moments for arbitrary measurable partitions (empty parts
  permitted). It does not by itself resolve prescribed positive
  masses or nontrivial equal-mass partitions of k>3 pieces.
- **Khot–Naor** Gaussian partition extremal reductions are cited
  in OpenAI-096 and are historical antecedents of the
  finite-score and power-diagram approach.

## Fixed-mass Gaussian problems and simplex antecedents

- Steven Heilman, *Euclidean Partitions Optimizing Noise
  Stability* (2012), https://arxiv.org/abs/1211.7138.
  Discusses the equal-mass Standard Simplex Conjecture,
  including the k=3 small-correlation case.
- Steven Heilman, Elchanan Mossel, Joe Neeman,
  *Standard Simplices and Pluralities are Not the Most Noise
  Stable* (2014), https://arxiv.org/abs/1403.0885.
  In particular, equal masses matter: unconstrained or
  unequal-mass simplex-optimality statements are not
  generally valid.
- Steven Heilman, *Stable Gaussian Minimal Bubbles* (2019),
  https://arxiv.org/abs/1901.03934. Discusses stability
  and fixed-volume Gaussian centroid optimization problems.
- Emanuel Milman and Joe Neeman, *The Gaussian Double-Bubble
  and Multi-Bubble Conjectures*, Annals of Mathematics 195
  (2022), https://annals.math.princeton.edu/2022/195-1/p02.
  This optimizes **Gaussian perimeter**, not squared first
  moments or the full positive-correlation noise-stability
  functional. Its conclusion must not be silently applied
  to our different objective.
- Abhijeet Mulgund, *Stochastic Domination of Gaussian
  Maxima by the Regular Simplex* (2026),
  https://arxiv.org/abs/2609.28452.
  This very recent work concerns Gaussian maximum comparison,
  directly adjacent to our order-statistic analysis, but
  it is not a general fixed-mass partition optimality theorem.

## Precise scope of the present note

- **Exact planar fan theory:** fixed-angle uniform lower bounds,
  complete phase transitions, nonuniform lower bounds,
  global three-sector sharp quadratic stability, and their
  rotation-invariant radial-law extensions. The active-face
  trigonometric proofs are self-contained. A targeted scan
  has not settled their historical novelty.
- **Global equal-mass asymptotic:** we obtain
  [2 log k - log log k - log(4pi) + O(1)]/k
  for all dimensions d>=k-1 via a halfspace
  centroid upper bound and an iid-Gaussian maximum
  lower construction. Gaussian maxima asymptotics
  and halfspace rearrangement are classical;
  we do not claim historic originality of their
  combination without a comprehensive literature
  review. Exact finite-k standard-simplex optimality
  remains outside the proof.
- **Regular-simplex equal-mass lower constructions:** exact
  first-moment values and strict inequalities versus the
  *planar fan comparator*. This does not establish
  all-partitions optimality, and Gaussian simplex constructions
  are standard objects in the prior literature.
- **Small positive-noise comparison:** tetrahedra versus
  quadrants, with a rationally bracketed first-Hermite
  certificate threshold. This is a two-explicit-partition
  comparison, not a resolution of Standard Simplex.
- **Ambient dimension reduction:** for k fixed positive
  cell masses, we prove exact stabilization of the
  first-moment optimum in dimension k-1 and cylindrical
  rigidity of attaining partitions. Related Gaussian
  dimension-reduction ideas occur in Khot–Naor-type
  Gaussian partition arguments; originality of the
  general reduction is not claimed.
- **Finite-dimensional fixed-mass dual and Laguerre property:**
  a fully proved unified reduction including degenerate
  score cases. Related first-variation/power-diagram ideas
  are classical; this is documented as a proof framework,
  not a historical novelty assertion.
- **Classical calibration:** the prescribed-mass two-cell
  halfspace optimum is classical, and the equal-three-cell
  global upper bound is explicitly inherited from OpenAI-096.

## Actual open problem after this work

For k>=4, prescribed positive masses p_i, and Gaussian dimension
d>=k-1, determine the global maximum of the squared first-moment
objective over **all** measurable partitions. In the equal-mass
case the regular simplex supplies a candidate and a certified
lower bound, but proving a matching universal upper bound
(or constructing a superior counterexample) remains essential.

Theorem 18 rewrites this as an exact finite-dimensional
max-min over score vectors and Laguerre prices. A genuine
next breakthrough would be a global inequality or
computer-verifiable semialgebraic/interval certificate
for this nonconvex outer problem. No such full certificate
is supplied or claimed here.

Further historical checking should include MathSciNet,
zbMATH, direct citations of Khot–Naor and Heilman, and
specialist trigonometric-inequality literature before any
journal submission or priority assertion.
