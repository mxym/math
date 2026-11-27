# Precise source mapping and comparison

1. A. de Oliveira Junior, Santiago Zamora, Jonatan Bohr Brask, Rafael
   Chaves, and Armin Tavakoli, *Quantum prepare-and-measure scenarios:
   concepts and methods*, [arXiv:2610.20725v1](https://arxiv.org/html/2610.20725v1)
   (14 October 2026).
   * Section IV.2, around Eq. (161), fixes the almost-dimension
     assumption: a common rank-$d$ projector has population
     at least $1-\epsilon_x$ for each state, not a fidelity to a
     fixed pure target. Its moment approach addresses broader correlations.
   * Section IV.7, Eq. (205), defines the normalized
     minimum-error correct-label probability. Eqs. (206)–(207) give
     the strict-dimension ceiling; at uniform prior and $d\le n$ it
     is $d/n$.
   * Eq. (221) and its following discussion give the same formula
     as our (2) as an **upper** bound, capped at 1 after
     $\epsilon=1-d/n$, and explicitly conjecture tightness for
     almost-dimension. It does not claim tightness for arbitrary
     prescribed target states (the separate fidelity assumption).
     The uniform Fourier attainment is the answer to that conjecture.

2. Jef Pauwels, Stefano Pironio, and Armin Tavakoli,
   *Information capacity of quantum communication under natural
   physical assumptions*, [arXiv:2405.07231v3](https://arxiv.org/html/2405.07231v3),
   [Quantum **9**, 1637 (2025)](https://doi.org/10.22331/q-2025-02-18-1637).
   The almost-dimension condition is Eq. (1), the guessing metric
   with uniform prior is Eq. (2), and the relevant upper bound is §5
   Eq. (8). The text after (8) explicitly reports evidence from
   numerical instances, not a general proof of tightness.
   Reference [58] is the [associated MATLAB seesaw](https://github.com/jefpauwels/SDISeesaw),
   not an analytical attainment theorem. The $d=1$ vacuum case
   is already analytically attained in Eq. (7); this note does not
   claim that case as new. Section 3 and the discussion after Eq. (8)
   describe peak and average shared randomness and note the
   bivariate concavity of the upper bound. The independent converse
   here gives an explicit binary-fidelity Hessian and includes a
   scalar allocation with arbitrary nonuniform priors and unequal
   budgets. The upper formula and existence of average-flag bounds
   themselves are not new.

3. Jef Pauwels, Stefano Pironio, Erik Woodhead, and Armin Tavakoli,
   *Almost qudits in the prepare-and-measure scenario*,
   [arXiv:2208.07887v2](https://arxiv.org/abs/2208.07887v2),
   [Phys. Rev. Lett. **129**, 250504 (2022)](https://doi.org/10.1103/PhysRevLett.129.250504).
   This introduces the rank/population model and a hierarchy; its
   exact random-access-code witness is not Eq. (221)'s single-setting
   minimum-error label guessing task. Moisés Alves, Tailan S. Sarubi,
   Vitor L. Sena, Alexandre B. Tacla, and Rafael Chaves,
   [arXiv:2611.08607v1](https://arxiv.org/html/2611.08607v1), §II/§III,
   use similar average-over-flag leakage, but their Eqs. (10)–(13)
   concern guessing the **measurement output** when the input(s)
   are known, which is a different objective.

4. Abhishek Mishra, Michele Masini, Maria Balanzó-Juandó,
   Armin Tavakoli, and Stefano Pironio,
   *Prepare-and-measure quantum key distribution from a bound
   on information leakage*,
   [arXiv:2610.37296v1](https://arxiv.org/html/2610.37296v1).
   Equations (4), (5), and (7) give the precise rescaled quantity
   $P_{{\rm g},n}=nP_{\rm g}$, its bound $G$ on $QE_0$, and
   data processing; Eq. (10) is the exact subspace ceiling.
   In §IV.2, Proposition 2 / Eq. (38) bound deviations from reference
   states by $\sum_x\sqrt{\epsilon_x}$, giving $d+n\sqrt\epsilon$
   for the common-subspace specialization with uniform deviation.
   The ensuing four-state example with four orthogonal exterior
   *product* side tags gets $2+2\sqrt{\epsilon(2-\epsilon)}$ in
   their rescaled units, not the general common-subspace
   optimum. Their one-modified-label example concerns a different
   prescribed ensemble and set of budgets. Neither example proves
   Eq. (221) tight for all dimensions and leakage. Section IV.3 /
   Eq. (40) separately treat a marginal fidelity condition with
   prior quantum correlations. That model does not satisfy the
   present theorem merely by being near a subspace on $Q$.
   Section VII explicitly leaves sequential/coherent extensions open.
   This note only supplies a sharper calibration when its own
   all-accessible-system or independent-classical-flag assumptions hold.

5. The diagonal realization of a rank-$d$ projection is the
   projection special case of the Schur–Horn theorem; e.g. Alfred
   Horn, *Doubly stochastic matrices and the diagonal of a rotation
   matrix*, [Amer. J. Math. **76**, 620–630 (1954)](https://doi.org/10.2307/2372705). Section 4 includes a
   self-contained proof for that special case.

The focused search on 2026-11-27 compared the published 2025 precursor,
the 2026 tutorial and its references, almost-qudit random-access and
output-randomness papers, and recent guessing/partial-dimension
theorems. It did not locate a previously published general
attainment proof for Eq. (221) or the heterogeneous scalar formula.
This is a scoped comparison, not a formal priority assertion.
