# Maximum entropy Gaussian covariance under exact linear invariants

This note answers two mathematical questions about the constrained covariance
step in [Lafferty–Roy, arXiv:2607.22450v2](https://arxiv.org/pdf/2607.22450v2).
It treats fixed Gaussian marginal variances and requires the linear invariant
to hold almost surely.

1. **One arbitrary linear invariant.** The unique maximum-entropy covariance
   on the maximal feasible support has a formula using one monotone scalar
   root. This includes unequal marginal variances, zero coefficients,
   saturated balance, and a no-solution test. Disjoint weighted constraints
   and common-weight laminar constraints reduce to independent blocks.
2. **When the log-det penalty preserves invariants exactly.** For any
   number of constraints, suppose the prescribed subspace itself permits
   a full-support correlation matrix. The finite-weight soft objective
   in Eq. (6) is exact if and only if the subspace projector commutes with
   its diagonal leverage matrix. Otherwise every optimizer has positive
   invariant variance at every positive penalty weight parameter, and the
   variance has a positive, explicitly characterized quadratic leading
   term as that parameter tends to zero. A convex norm penalty can
   enforce exactness instead, as can the direct equality-constrained problem.

The paper's equal-weight example is in the exact class, but not all
heterogeneous weights are. These are covariance optimization statements;
they do not claim an issue with deployed privacy systems, an optimal
privacy/utility covariance, or an extension to independently scaled
Laplace marginals. For clarity the proof states the standard exact
Gaussian privacy calibration on the invariant subspace separately.

See [proof](PROOF.md), [sources](SOURCES.md), and [replay output](RESULTS.txt).

Replay with Python 3, NumPy, SciPy and SymPy: sh replay.sh.
