# Final manuscript review

8 October 2026. Internal independent model review by the combinatorics
research agent; not external peer review or full formalization.

Reviewed file: `research/gaussian-balanced-four-global/paper.md`.
SHA-256 at review: `b0948a0892df77cf379484466984091977265b8190672c62ad0170d1a436561c`.

The earlier detailed review is
`/workspace/scratch/gaussian-mountain-pass/COMBINATORICS_REVIEW.md`.
The final standalone manuscript was re-read in full, including its
differences from the scratch proof.

## Findings

No substantive gap was found in the complete argument as written.
The constrained projection flow produces the upper-normal sign needed
for the PSD top-eigenspace condition. The extra factor (1-epsilon) in
the regularized gradient is positive, so does not change that condition.
The residual identity, uniform multiplier bounds, score separation,
price compactness, boundary facet convergence and self-moment scaling
are all complete and have the stated constants.

The rank-two obstruction is now explicitly stated with stationarity
and spectral hypotheses, without an implicit global-maximizer premise.
All convex-hull degeneracies are covered. Its three-cell and profile
inputs are proved. The rank-one trace contradiction has the correct
factor two and denominator.

The local Hessian was independently recomputed as documented in the
previous review. Its negative coefficients yield strict local maximality
on trace-one covariances after removing rotations and fixing score norm.
The multi-bubble theorem's perimeter normalization and regular constant
were checked against the original Milman--Neeman text.

Fractional partitions satisfy the same pointwise assignment inequality:
their weighted average winning score is at most the maximum. Equality
with distinct regular scores forces the fractional labels to be the
unique winning indicator almost everywhere, so the equality extension
adds no hidden relaxation case.

The standalone proof uses no boundary C-squared claim. It only invokes
smoothness at regularized positive covariances and dominated convergence
at the separated boundary. This removes a potentially delicate boundary
variation dependency from the older rank-rigidity route.

One minor wording correction was requested: in Section 5 the rank-two
4-by-3 matrix has a two-dimensional column space, rather than literally
two columns. The intended argument is mathematically unchanged.

## Scope

The proof settles exactly four equal Gaussian cell masses and the
first-moment objective. It does not establish positive-correlation noise
stability, arbitrary masses, more than four cells, or covariance concavity.
The partial Lean diagnostics remain partial; all imported analytic
theorems are stated as dependencies. Internal review has not been
represented as external mathematician review.

Additional bibliographic bridge: Milman--Neeman states minimizers as
simplicial Voronoi clusters. In the equal-quarter case centrality follows
from uniqueness of balanced prices for fixed regular full-rank scores:
symmetry gives equal prices, and a nonzero effective translation would
give unequal prices. This justifies the precise central-perimeter
corollary imported in Section 7.

The exported statements in `formal/Algebra.lean` were also read.
They use explicit scalar hypotheses and match their indicated algebraic
steps. `FalseBound.lean` is an intentionally invalid weakened-profile
statement for an expected-failure guard, not a proved theorem.

Final verification after the requested manuscript clarifications:
`paper.md` SHA-256
`f86af0ff6f1eb32a8f7fbdb8105aa0a5c4b4d82e6cd307ea1b167a7bc0cb9d24`.
Verified the explicit fractional moment bound using
(T-q)(f-1_{T>=q})<=0, dominated convergence of first moments in Lemma 5,
the equal-price symmetry bridge to the central multi-bubble minimizer,
and the two-dimensional column-space wording. All four clarifications
are correct. No additional substantive issue was found.

Final Eq. (21) notation check: the residual identity explicitly uses trace of the matrix square, `tr[(L-epsilon - mu-epsilon P)^2]`, not square of its trace. This matches the reviewed algebra. Manuscript SHA-256 after this notation correction: `570518f50ff0c656fb52cd9d7fdcb59d19fcfbd24260d180c5d2b4b28ea0e70d`.
