# Gaussian centroid partitions: arbitrary-mass two-collision envelope

**Status:** self-contained analytical research note with a standalone
exact-arithmetic checker. **No claim of world-first novelty or full
Standard Simplex optimality.**

This work continues the mass-constrained Gaussian partition program
associated with [OpenAI Mathematics, result 096][oai096] and our
[Gaussian propeller / fixed-mass companion][companion], but removes
the equal-mass and near-equal-mass hypotheses from the asymptotic
first-moment theory.

## Main result (all prescribed positive masses)

Let p=(p_1,...,p_k) be any strictly positive probability vector,
and let d>=k-1. Define

    M_d(p) = sup sum_i || integral_{A_i} x dgamma_d(x) ||^2,

over all measurable Gaussian partitions with gamma_d(A_i)=p_i.
Set t_i=Phi^{-1}(1-p_i), and let

    U(p) = sum_i phi(t_i)^2,
    Q(p) = sum_i p_i^2.

Then our analytic theorem proves the **fully nonasymptotic bound**

    0 <= U(p) - M_d(p) <= 2 Q(p).

The upper quantity U is the sum of separately achievable
one-cell Gaussian halfspace maxima. The lower inequality is
witnessed by an explicit **sequential-threshold partition**
of R^(k-1), with exactly the prescribed cell masses.

No bounded ratio p_max/p_min is needed, and the dimension
condition is independent of how unbalanced the masses are.
Q(p) is the collision probability of two independent
categorical draws with law p.

The key lemmas are:

1. The **squared upper Gaussian hazard** is globally
   2-Lipschitz in logarithmic tail probability:
   0 <= h(q1)^2 - h(q2)^2 <= 2 log(q2/q1)
   for 0<q1<=q2<1.
2. After sorting masses decreasing, the **weighted residual
   mass entropy** obeys
   sum_i p_i^2 log(1/S_i) <= sum_i p_i^2,
   S_i=sum_{j>=i}p_j.
3. The final, unconditioned cell is handled *without loss*
   by Gaussian exponential moments and Jensen's inequality:
   phi(Phi^{-1}(1-p))^2 <= 2 p^2 log(1/p).

## Consequences

The manuscript also proves:

- A universal two-log-scale formula with **explicit constants**
  6 and 3:
  B(p)-6 Q(p) <= M_d(p) <= B(p)+3 Q(p),
  B(p)=sum_i p_i^2 [2 log(1/p_i) - log^+ log(1/p_i)].
- If max_i p_i -> 0, the global optimum is asymptotic to
  2 sum_i p_i^2 log(1/p_i), **without any constraint on
  the ratio of the largest to smallest masses**; the
  weighted log-log term is controlled to O(Q(p)).
- For p_i between a/k and b/k, the exact leading coefficients
  are (2 log k - log log k - log(4pi)) Q(p) + O_{a,b}(1/k).
- The squared Gaussian upper-tail hazard also obeys the globally
  sharpened scalar bound B(q)-4 <= h(q)^2 <= B(q)+3,
  proved from elementary Mills inequalities and a Gaussian
  exponential-moment bound. This replaces the older 17/17
  scalar estimates.
- The constructive threshold partition is globally
  asymptotically optimal as p_max->0, and near-optimal
  partitions satisfy a quantitative collision-weighted
  moment-deficit concentration statement.
- For nonnegative Gaussian correlation rho<1, the same
  partition approximates the **full noise-stability**
  optimum with additive error at most
  2*rho*Q(p)+rho^2*(1-Q(p)).
- All coordinates of the explicit threshold partition's
  first moments have exact one-dimensional formulas,
  documented in the manuscript.

These are statements about the **global measurable Gaussian
partition problem**, not merely a planar fan subclass.

## Contents and reproducibility

- [paper.md](paper.md): definitions, theorem statements, full
  analytical proofs, all boundary conditions, and scope.
- [check_exact.py](check_exact.py): stand-alone Python 3
  standard-library script; exact fraction and outward-rational
  log interval arithmetic, no floating point.
- [results/check_report.txt](results/check_report.txt):
  reproducible text output, including a negative control.
- [AUDIT.md](AUDIT.md): independent proof-scope checklist.
- [LITERATURE.md](LITERATURE.md): provisional novelty screen
  and attribution.
- [SHA256SUMS](SHA256SUMS): reproducibility manifest.

Replay:

    python3 check_exact.py
    python3 check_exact.py --quick
    sha256sum -c SHA256SUMS

The finite checker confirms exactly specified cell masses,
the algebraic telescoping, interval-enclosed sample residual
entropies (including highly nonuniform vectors), and a
deliberately **unsorted counterexample** to show the ordering
hypothesis matters. **Finite checks are not a proof of the
universal theorem.** Its proof is analytic and complete in
paper.md.

## Scope and important qualifications

We do not prove exact finite-k global simplex optimality
for k>=4. The universal additive constant 2 is valid,
but not established as the best possible. A separate
[dimension-rate continuation](../gaussian-centroid-dimension-rate/README.md)
shows that one-pass stairs use the full 2/k
budget asymptotically for equal masses, while
new hierarchical Gaussian partitions achieve
optimal-order O_epsilon(log k) dimension at
every fixed relative accuracy. The bibliography
has not undergone comprehensive specialist review, and
historical mathematical priority is not asserted.

[oai096]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf
[companion]: https://github.com/mxym/math/tree/4efb271ef56070bd5b3e300d33dfafb547fceacf/research/gaussian-propeller-balanced-fans
