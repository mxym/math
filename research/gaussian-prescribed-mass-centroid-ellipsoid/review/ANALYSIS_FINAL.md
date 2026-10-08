# Final standalone prescribed-quota paper: independent analysis review

Date: 8 October 2026. Reviewed source
`/workspace/scratch/gaussian-prescribed-quota/paper.md`,
SHA256 `2a5d8f97bf3812aba1045b395d94c6efbddceb48310ce63fd50632a1a8ed4698`.

The root wrote this standalone paper after receiving the independent derivation
`PRESCRIBED_QUOTA_ELLIPSOID.md` (frozen SHA256
`777c477aa453d1ad5b5e298564e09bf76764e6d6fa0e2f526d8b9da86a43f0dd`).
I read the complete standalone source and checked its new layout, all equation
numbers and claims against the derivation and the primary perimeter source.
The detailed mathematical checks are recorded in `PRESCRIBED_QUOTA_REVIEW.md`.

## Final-copy checks

- Abstract and Theorem 1 assert the label-metric first-moment inequality for
  all ordinary/fractional functions of positive prescribed masses, with every
  k>=2 and d>=1; they do not assert the false unweighted unequal-mass conjecture,
  the full functional multi-bubble theorem, noise stability or worldwide first.
- The model is translated by the unique quota price vector in its centered
  gauge, and every facet area is positive. H_p is the interface-area Laplacian,
  L_p=H_p/ell_* is the score Laplacian, ell_*=sqrt(2/(k-1)). The source normalizes
  I(p) as sum of pair interfaces and states Hess I=-H_p^+ only on 1-perp.
- Equations (9)--(11) have consistent factors 2 and n: C=tr LQ, tr L=2sum w,
  S^2<=C tr L/2 and I(p)^2=c_p^2 n/2. Thus C tr L/n>=c_p^2 holds for precisely
  the positive quotas used in the imported theorem's dimension k-1.
- Equations (13)--(16) retain the generally nonzero initial derivative
  h'(0)=c_p tr[L_p(Q-Q_*)]. The exact tangent deficit is
  c_p tr L_pQ-C_p(Q)^2, rather than a Euclidean covariance maximum assertion.
  Endpoint continuity is used at a potentially singular Q, not facet or
  derivative continuity there. The positive improper integral converges by its
  exact finite endpoint difference; at zero the integrand is bounded.
- All equalities in (12) require Q=sQ_* including Q=0. Positive interior facet
  weights force equal score edge lengths; double-centering then gives the
  regular Gram. This classifies boundary equality without rank analysis.
- Pseudoinverse moment duality (18) uses that moment columns sum to zero and
  L_p^+L_pL_p^+=L_p^+. The feasible upper score bound remains valid for repeated
  score rows, so no nonexistent unique-price assignment at rank degeneracy is
  assumed. Equality restores full rank, makes ties null, and forces the
  fractional labels to ordinary model indicators. The low-dimensional case
  is strictly below the bound. The k=2 and zero-moment cases are explicit.
- The independent price differentiation of the established profile Hessian
  has the correct sign: D_lambda masses=-L_p, D_p lambda=-L_p^+, gradient c_p
  equals lambda and c_p=ell_* I. Thus Hess I=-H_p^+, matching [MN22, Prop 2.4].
- The uniform specialization L_p=c_k P recovers the prior equal-mass bound,
  while its publication is counted as the prior theorem, not as another
  independently solved conjecture. Source screening and analytic/Lean/model
  review limits are explicit and appropriately separate.

## Conclusion and scope limits

No substantive proof gap or mathematical mismatch identified in this final
standalone source. This is an internal independent model review, not external
human peer review. It is not a full Lean formalization. The Gaussian measure,
Gaussian flux/assignment calculus and multi-bubble input remain fully written
analytic arguments and an attributed established theorem. The accompanying
new Lean comparison only certifies the real one-variable implication with its
regularity, derivative and endpoint hypotheses exposed.

Any later source edit requires a new hash and review of the changed text.
PDF rendering is the root's separate visual/layout audit; this record checks
mathematical Markdown source rather than verifying every exported PDF glyph.

## Confirmed author metadata and final source update

The final source SHA256 is `bef41c3cdf68e11ee5b4d8eb31742952170e1dcca1d510f336f31b497e156126`. Changes reviewed: the author is
Yongxian Zhang with the confirmed institution, correspondence and ORCID; an
author information/disclosures section explicitly states no external funding,
no institutional endorsement and the actual OpenAI-assisted research/proof/
writing/code/internal-review workflow. It correctly distinguishes internal
model reviews from external human peer review and partial checks from the
complete written analytic endpoint. The profile is called a k-cell profile.

Verification: removing exactly the appended author/disclosure section and
reversing the author and k-cell terminology changes reconstructs the previous
source **byte for byte**, as certified by its original SHA256
`2a5d8f97bf3812aba1045b395d94c6efbddceb48310ce63fd50632a1a8ed4698`.
Thus no mathematical statement, proof or reference changed between these
reviewed source versions. The prior mathematical audit carries over to the
new final SHA above; no new analytic premise or human-review claim was added.
