# Final-copy review of the prescribed-mass Gaussian first-moment theorem

Reviewer: `conjecture_combinatorics`, 8 October 2026 UTC.
This is an internal adversarial model review, not external expert peer review.

Reviewed standalone manuscript:
`/workspace/scratch/gaussian-prescribed-quota/paper.md`.

SHA-256:
`2a5d8f97bf3812aba1045b395d94c6efbddceb48310ce63fd50632a1a8ed4698`.

I read the complete final copy and checked it against the independently
reviewed analysis-agent derivation. No substantive mathematical gap was
found in the stated positive-mass theorem or equality classification.

The detailed independent calculation review is
`PRESCRIBED_QUOTA_REVIEW.md` in this scratch directory. Its checks of
Gaussian flux, covariance derivatives, nonzero initial slope, weighted
Cauchy and imported perimeter normalization, singular endpoints,
homogeneous equality rays, pseudoinverse duality, fractional equality
and exact Milman--Neeman Hessian convention apply unchanged to this copy.

Additional final-copy checks:

1. Section 1 fixes k>=2, n=k-1, all p_i>0, and the fixed quota vector.
   The theorem asserts the sharp weighted functional bound, not the
   false unequal-mass unweighted simplex conjecture. The lower-dimensional
   assertion is pointwise strictness rather than a sharp supremum claim.

2. Section 2's added independent profile-Hessian normalization is correct.
   The model mass Jacobian in price coordinates is -L_p, the quota-envelope
   derivative of c_p is the zero-sum balancing price vector, and hence
   Hess(c_p)=-L_p^+. Since c_p=ell_* I(p), this gives
   Hess(I)=-L_p^+/ell_*=-H_p^+. All derivatives and inverses here are on
   the Euclidean tangent space 1-perp; columns of the moment matrix lie
   in that space. There is no extra factor from simplex coordinates.

3. Equation (15) retains the general initial derivative correctly.
   The endpoint difference in (16) is exactly c_p tr(L_pQ)-C_p(Q)^2.
   The improper-integral argument uses finite quotient limits, and the
   smooth-zero-endpoint O(t^2) integrand statement is consistent with a
   nonzero first derivative. Equation (17)'s coefficient 2/n is correct.

4. Theorem 3 explicitly includes every centered PSD covariance, with
   equality exactly on sQ_* for s>=0. Its normalization and endpoint
   continuity argument cover Q=0 and singular nonzero Q without boundary
   differentiation. The finite double-centering equality argument is valid.

5. Equation (18) uses E=<L_p^+ B,B> and correctly reduces its trace by
   L_p^+L_pL_p^+=L_p^+. Equality forces the regular score Gram matrix
   with scale one, null ties and the uniquely quota-balanced ordinary
   winners. The converse model calculation attains the bound exactly.

6. Scope and dependency statements correctly separate imported geometry,
   partial Lean checks and full written analysis. No full simplex-valued
   Bobkov theorem, positive-correlation noise-stability result, external
   expert approval, or worldwide first-publication assertion is claimed.

This review supplies mathematical checking only. Literature equivalence
and historical novelty remain separate source-screen questions. The
source is frozen for the parent publication workflow; I have not modified
the manuscript, staged files, committed, pushed or created a release.

## Author/disclosure and terminology final-copy addendum

Reviewed updated source SHA-256:
`bef41c3cdf68e11ee5b4d8eb31742952170e1dcca1d510f336f31b497e156126`.

The title-page author is now Yongxian Zhang. The added affiliation,
correspondence address and ORCID match the user-confirmed `AUTHOR.md`.
The funding and AI-assistance statements accurately disclose independent
work, no external funding and internal model reviews; institutional
endorsement and external human peer review are not asserted. Section 1
now uses the precise term “k-cell profile”, removing the earlier
k-bubble/k-minus-one-bubble terminology ambiguity. The definitions,
theorems, numbered formulas (1)--(18), proofs and equality scope remain
mathematically unchanged. This addendum records no new formal or novelty
claim, and the previous mathematical review conclusion still applies.
