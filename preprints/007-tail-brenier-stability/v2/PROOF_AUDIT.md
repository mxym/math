# Version 2 proof audit

## Reconciliation with parallel manuscript 001 v3

The v3 source was already public at 5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3 before this manuscript's full v1 source. Its general target-tail estimate, finite-moment exponent, hard-boundary sharpness, and Gaussian/global-bounded-Hessian estimates are acknowledged rather than rebranded as new. This pass checked its signed-square/minimum-weight interpolation and the two-atom strip mechanism. It did not externally certify all of manuscript 001's finite-cell regularity or source potential estimates.

The v2 additional results are the BV-density theorem retained from v1, the superquadratic translation-ratio criterion and fixed-product sharpness, and the single smooth full-support counterexample. The latter is not contained in the hard-boundary examples read in 001 v3.

## New counterexample: closed proof obligations

1. The smooth step is monotone, flat at both joining endpoints, and symmetric about 1/2. Its primitive is convex and exactly linear after one. The infinite source potential sum is locally finite.
2. All layers are added with nonnegative convex curvature. The resulting density is strictly positive C-infinity on all of R^d, with Hessian of its negative log at least I and finite normalization.
3. The recursive scale exponent dominates both the pre-layer potential B_n and slope D_n. Consequently a_n D_n tends to zero, B_n/|log a_n| tends to zero, and the post-layer tail is negligible compared with beta_n a_n. The source is fixed independently of q.
4. On bounded rescaled coordinates, the pre-layer density is asymptotically constant. A global convex-tangent bound supplies the Gaussian-integrable majorant t_+ exp(t_+)+1, needed because the transverse Gaussian coordinate is unbounded.
5. The cell-mass matching equation has a unique solution by strict monotonicity. Dominated convergence and bracketing bound and identify that solution. Moving arguments are justified by monotonicity and continuity of the limiting profile.
6. Two rare atoms have exactly unit qth moment. Explicit convex hinge potentials identify their Brenier maps; no approximate optimizer or solver output is used.
7. The target coupling cost and common-source map cost have exact formulas. The cell symmetric-difference mass is asymptotic to a strictly positive multiple of the rare mass.
8. Log m_n/log a_n tends to one. This yields divergence for every exponent greater than (q-2)/(3q-2), for every q>2, and the q=2 nonuniformity endpoint.
9. Matching upper bounds use the explicitly identified source potential estimate from 001. The lower-bound counterexample does not depend on that estimate.

## Positive results

The minimum-weight argument controls both finite-difference endpoints, while the signed-square inequality converts monotone derivative increments into integrals of translated density differences. The L^s translation-ratio norm justifies all signed changes of variables. Polynomial confinement dominates the exponential of polynomial gradient growth. Product marginal estimates allow unequal confinement orders. Fixed-product three-atom sharpness uses the actual first two source marginals, not a Gaussian substituted for them.

## Evidence and limits

The complete 12-page local PDF was compiled twice and every rendered page inspected. Exact finite checks comprise the earlier 6000 interpolation inequalities, 15 ramp identities, six exponent cases, plus 220 layer-parameter cases and 936 two-atom cost identities; optimized Python mode also passed. The tests do not compute an infinite-density normalizer or certify the analytic limits. There is no independent human peer review, proof-assistant formalization, or novelty certification. The source-translation condition is sufficient; no necessary-and-sufficient classification of all smooth sources is claimed.
