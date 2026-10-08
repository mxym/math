# Source attribution and provisional novelty assessment

This is an **initial bibliographic screen**, not a systematic
MathSciNet / zbMATH / Google Scholar review, and it creates no
claim of mathematical world-first priority.

## Upstream

1. OpenAI, *The Gaussian propeller bound in every dimension*
   (September 24, 2026), result family 096 of
   https://github.com/openai/math; pinned comparator:
   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf.
   Its unrestricted unweighted global moment theorem
   does not supply an exact fixed-mass global solution.
2. Our previous independent result and full fixed-mass
   dual framework:
   https://github.com/mxym/math/tree/4efb271ef56070bd5b3e300d33dfafb547fceacf/research/gaussian-propeller-balanced-fans.
   The prior result includes sharp planar fan
   optimization, an exact finite-dimensional
   fixed-mass dual, dimension saturation,
   and a two-term asymptotic for **equal** Gaussian
   cell masses. The present note extends those
   asymptotics to *arbitrary unequal* masses and
   adds a nonasymptotic collision-mass error bound.

## Prior mathematical themes

- **One-cell Gaussian halfspace rearrangement** is
  classical. So are Gaussian Mills bounds, normal
  exponential moments and Jensen's inequality.
- **Gaussian Level-1 / Fourier entropy estimates**
  of the form W_1(A)<=2p^2 log(1/p) have
  substantial antecedents in Gaussian and Boolean
  harmonic analysis. The scalar bound is proved
  directly here by a one-line exponential-moment
  argument; it is not claimed new.
- **Biased halfspaces, noise sensitivity, and local
  Chernoff inequalities**, Discrete Analysis (2019):
  https://discreteanalysisjournal.com/article/10234-biased-halfspaces-noise-sensitivity-and-local-chernoff-inequalities.
  This studies biased first-degree Fourier weights
  in the Boolean context; it is related but does not,
  from the material screened, provide the present
  all-mass Gaussian partition construction.
- Steven Heilman, *Euclidean Partitions Optimizing Noise
  Stability* (2012): https://arxiv.org/abs/1211.7138.
  Historical background for Gaussian partition
  noise stability and Standard Simplex questions.
- Heilman, Mossel and Neeman,
  *Standard Simplices and Pluralities are Not the
  Most Noise Stable* (2014):
  https://arxiv.org/abs/1403.0885.
  Motivation to state precisely which Gaussian
  noise functionals and mass restrictions are
  addressed; the noise-stability questions are
  not automatically interchangeable.
- Khot--Naor Gaussian partition reductions
  (cited in OpenAI-096) are antecedents of
  finite-score and power-diagram ideas.

## Precise mathematical additions asserted here

- One explicit construction of **mutually disjoint**
  Gaussian cells with exactly prescribed positive
  masses, using *k-1 independent threshold coordinates*.
- A globally valid 2-Lipschitz inequality for
  the squared normal upper-tail conditional mean
  under logarithmic mass changes.
- A sorted-residual-mass quadratic entropy lemma
  and a proof that its sorting condition is essential.
- An additive **2 sum p_i^2** comparison to the
  individually optimal halfspace centroid envelope,
  independent of every mass ratio and ambient
  dimension d>=k-1.
- The explicit **19/17** weighted-entropy two-sided
  envelope, including arbitrary-mass two-log
  asymptotics and collision-weighted concentration
  consequences.
- A full nonnegative-correlation Gaussian
  noise-stability approximation bound built from
  the same explicit partition.

These are statements proved in this manuscript.
Whether some or all were previously known in
an equivalent form requires further historical
verification. Do **not** label this manuscript
a first solution or first proof.

## Open problems not solved

- Exact optimality and equality classification of
  the Standard Simplex candidate in the unrestricted
  equal-mass Gaussian centroid problem for each
  fixed k>=4.
- The optimal coefficient (possibly below 2) in
  the mass-independent additive envelope.
- Sharpness of the stated bounds for very uneven
  masses at finite k.
- Extending the universal bound to d<k-1 with
  an analogous dimension-uniform constant.

The public GitHub commit timestamps document
a mathematical disclosure, not an automatic
priority determination.
