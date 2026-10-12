# Proof audit: logarithmic density and similarity, v1.1

## Scope

Complete written analytic/probabilistic argument. No independent peer review or proof-assistant formalization is claimed. The normalized rational-cover verifier checks only supplied finite certificates; its toy tests do not certify the full small-measure construction.

## Checked dependencies

1. **Upper Banach density.** Subadditivity gives the limit and a uniform upper-count bound. To place a template after H, use the translated tail S_H={j>=1:j+H in S}. Merely deleting a prefix does not by itself force an interval's starting point; the earlier draft's wording has been repaired explicitly.
2. **Density flattening.** The complement of a window in its template has at most two intervals. A near-maximal total count minus uniform complementary upper counts fills every window; constants are chosen before the template translate.
3. **Addresses.** One parity of logarithmic indices has positive density. Dyadic annular inequalities separate all tested keys, including the exposed center key. Nesting preserves distinctness at finer terminal grids.
4. **Routes and exposure.** Every tested ancestor decision precedes the test edge in preorder. Exposing all center selectors does not expose tested selector entries. Conditional on all selectors, distinct tests use distinct terminal entries even if their routes share other selector entries.
5. **Continuous scales.** The finite representative set includes grid-crossing parameter values themselves, not just complementary intervals. Its entropy bound is local to each edge and its subtree.
6. **Exceptional centers.** The residual set is closed by compact projection. An open neighborhood repairs every residual center using the null tail. An almost-everywhere conclusion is not substituted for a universal one.
7. **Quantifiers and measure budget.** Apply normalized blockers to every dyadic dilation and every tail, using a summable two-index budget, and reflect for negative scales. Every copy has infinitely many hits. Countably many configurations use one further summable budget.
8. **Effective certificates.** Rational open strips are checked over the full closed parameter rectangle. Singleton complementary gaps are retained. Compactness gives finite rational certificates when the prescribed points are rational; exhaustive enumeration terminates under the theorem's density hypothesis, with no feasible runtime claim.
9. **Applications.** Squarefree exponents have positive density by a direct union bound. An infinite arithmetic progression contains a multiple of p^2 for p coprime to its step; this rules out an affine full geometric sequence inside the squarefree configuration.

## Limits

No claim for the zero-upper-Banach-density index sets {n^2} or {2^n}. No certificate for an uncomputed global avoiding set is presented. No unrestricted Erdos similarity solution or priority determination is claimed.

## Computational evidence

`verification/check_cover.py --self-test` passes six exact regression cases. The true toy cover has density 9/10; endpoint-only and singleton-gap failures return rational witnesses. All arithmetic is rational and endpoint comparisons are non-strict for the closed complement.
