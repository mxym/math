# Primary sources and boundaries of the claims

- Ryan Lafferty and Anindya Roy,
  [A Maximum Entropy Implementation of Differential Privacy Under Linear
  Invariants, arXiv:2607.22450v2, 15 November 2026](https://arxiv.org/pdf/2607.22450v2).
  Section 3.2, Eq. (3), sets \(B=\mathsf D A^{\mathsf T}\) and
  \(RB=0\). Section 3.3 Eq. (6) and Algorithm 2 define the soft
  log-det objective analyzed here. The compression analyzed throughout
  is explicitly the orthogonal complement of \(\operatorname{col}B\)
  from the derivation of (6), with positive diagonal scales.
  Theorem 2, Eq. (7)–(8) reduce general feasibility to the smaller
  SDP and give the graph factorization; Corollary 1 gives one-vector
  balance, and Theorem 3 gives the max-rank relative-interior statement.
  These are antecedents, not results claimed here. Section 5.1
  Eq. (10) gives the equal-weight example, and Remark 2
  notes the difficulty of a conditional construction with prescribed
  unequal marginal variances. Our scalar solution supplies that
  Gaussian construction. Theorem 2 and Theorem 3 of this note clarify
  exactly when the soft program (6), rather than the strict constraints,
  preserves the specified linear invariants.
  Independently, the statement of source Theorem 1 (printed pp. 6–7)
  drops a factor of \(\sigma\) in its displayed \(t_{a,\varepsilon}\),
  present in its appendix derivation (printed pp. 23–24);
  §5 here uses the standard analytic Gaussian formula. These are
  precise mathematical points, not claims about a deployment.
  The current v2 is used throughout; the v1 HTML is not substituted
  for its revised Theorem 2.
- Wayne Barrett and Stephen Piercé, [Null spaces of correlation matrices,
  LAA 368 (2003), 129–157](https://doi.org/10.1016/S0024-3795(02)00667-5),
  and James Saunderson, Venkat Chandrasekaran, Pablo Parrilo and Alan
  Willsky, [Diagonal and low-rank matrix decompositions, correlation
  matrices, and ellipsoid fitting](https://doi.org/10.1137/120872516),
  §3, give feasibility context, including the established one-dimensional
  balanced-subspace criterion (also of Ledermann and Delorme–Poljak)
  and SDP duality. We do not claim to newly solve general nullspace
  realizability.
- Carole Bernard, Oleg Bondarenko and Steven Vanduffel,
  [Rearrangement algorithm and maximum entropy, Ann. Oper. Res. 261
  (2018), 107–134](https://doi.org/10.1007/s10479-017-2612-2),
  §3.1, Eq. (3.3), Proposition 3.7 and Remark 3.10, already formulate
  the equivalent maximum determinant problem for prescribed Gaussian
  marginal variances and variance of their sum, using numerical
  optimization. In the strict one-invariant case our graph coordinate
  \(C\) is exactly of this form with prescribed sum variance one.
  The claim is the monotone single-root solution and its branches,
  not first formulation of the constrained maximum determinant.
- Lieven Vandenberghe, Stephen Boyd and Shao-Po Wu,
  [Determinant maximization with linear matrix inequality constraints](https://www.seas.ucla.edu/~vandenbe/publications/maxdet_rev.pdf),
  and Arthur P. Dempster, [Covariance selection](https://websites.umich.edu/~jizhu/jizhu/covar/Dempster-Biometrics72.pdf),
  are general antecedents for the standard log-det optimality test.
  General approximate versus exact penalty ideas are standard (e.g.
  [Nocedal–Wright's optimization treatment](https://doi.org/10.1007/978-0-387-40065-5)).
  Our claims are the explicit projector characterization and covariance,
  exact residual coefficient for the concrete log-det elliptope program,
  and the specialized convex norm repair.
- Borja Balle and Yu-Xiang Wang,
  [Improving the Gaussian mechanism for differential privacy:
  analytical calibration and optimal denoising](https://proceedings.mlr.press/v80/balle18a.html),
  Theorem 8, provide the exact scalar Gaussian profile. Only the
  explicit use on the prescribed support is included here; the
  privacy profile itself is not new.

Bounded searches on 2026-11-27 for fixed diagonal and specified null
vector maximum entropy, max-det correlation with specified aggregate
variance, and log-det exactness with correlation/projector leverage,
including the cited primary works, found no matching scalar root
classification or leverage/residual theorem. This is not a priority
guarantee. Nothing here treats the shape minimizing a worst-neighbor
distance, deployment privacy, or a general jointly mixable
non-Gaussian family.
