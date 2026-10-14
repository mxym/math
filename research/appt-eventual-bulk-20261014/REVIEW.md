# Independent ordinary review: exact eventual APPT bulk entropy

Reviewer: separately authorized review subagent `/root/ordinary_review_bulk`, an OpenAI AI assistant. This is internal ordinary mathematical review, not human peer review, a Lean audit or priority certification.

## Verdict and literal scope

No blocking mathematical gap was found. F1 and F2 give eventual exact optimization over actual all-unitary APPT states for fixed m >= 3, with the stated positive lower order bound. F4 gives the uniform compact-order rounding expansion. F3 concerns only the single-halfspace relaxation and explicitly uses a nonAPPT competitor.

The initial manuscript and map were completely read before this record:

| File | Physical lines actually read | Literal SHA-256 |
| --- | --- | --- |
| PAPER.md | 1–358, all 358 lines | 58860e1dd5f35b92a704921da86aa27eca6dc5a08abf308f5956e8b457e6c384 |
| THEOREM_MAP.md | 1–22, all 22 lines | 59a7986a72a9604309fe2c6be278192277d61d5f2f8bb79b9527cf5e0abb3020 |

The complete initial new-mathematics count is **380**. There was no subsequent source delta. LITERATURE.md 1–37 and README.md 1–32 were read separately as support; their 69 lines are not added to 380. Exact support/predecessor hashes and ranges are in [REVIEW.json](REVIEW.json).

## Independent mathematical checks

The physical implication was derived directly. A maximal m-Schmidt projector has R negative eigenvalues and K positive eigenvalues, each of absolute size 1/m. The global unitary in the APPT definition can assign the largest R state eigenvalues to the negative directions and the smallest K to the positive directions. This proves the necessary halfspace for actual matrices; it does not make that halfspace sufficient.

The gap expansion x_i = i(lambda_i-lambda_(i+1)) is an affine bijection with the standard simplex. A supported perturbation preserves trace and, on the boundary, the one halfspace equality. This proves the complete vertex list. There is exactly one zero-sign old vertex, u_(D-m). Two-coordinate boundary supports with a zero sign and a nonzero sign cannot occur. Opposite-sign edge cuts produce the two positive levels in F10, with the support loss log(D/j) retained in F11.

Direct differentiation gives the stationary factor in F12 and the strict ratio derivative in F13. Both formulas have their stated removable limits at order one. The maximizer stays in the interior on a compact positive order interval. The bulk value and finite ratio gaps have positive minima there. Early indices have finitely many high coordinates; late indices have finitely many low or zero coordinates. Their deficits are uniformly O(1/D). Central competitors with s >= 1 have a strictly smaller ratio. These facts justify one dimension threshold for every order in the interval.

For arbitrary projection P', its diagonal weights in a partial-transposed pure-projector eigenbasis lie between zero and one. The total negative eigenvalue sum is bounded below by -(m-1)/2. Since t=2/(m-1), every (I+tP')^Gamma is positive. Thus every projection rank and every global orbit is physically APPT. This proves actual attainment rather than an outer-spectral assertion.

Strict convexity above order one, strict concavity of the power sum below one, and strict entropy concavity at one eliminate every nonvertex minimizer of the relaxation, including boundary spectra with zeros. Actual spectra lie inside the relaxation and every winning bulk vertex is actual APPT. The spectral theorem gives exactly the matrix-level projection classification, retaining every exactly winning neighboring rank and every global orbit.

## The growing-order estimate

The continuous moment can be derived without an asymptotic guess. Put Q=r^alpha and b=r-1. At the stationary point,

    numerator = (Q-r)/(b(alpha-1)),
    normalization = alpha(Q-r)/((alpha-1)(Q-1)).

For alpha > 1 this gives

    F_r = (alpha-1)^(alpha-1)(Q-1)^alpha
          / [b alpha^alpha (Q-r)^(alpha-1)].

Consequently F_r ~ r^alpha/[e(r-1)alpha]. Only finitely many fixed ratios are compared. Uniformly on the complete real band, every nonbulk moment relative to F_q is bounded by

    C alpha/q^alpha
      + C max_s(q_s/q)^alpha
      + C alpha(m-1)^alpha/D.

The first two terms become uniformly small after choosing a fixed A0. If c log(m-1) < 1, the final term is at most

    C c log(D) D^(c log(m-1)-1),

which tends to zero uniformly for all alpha <= c logD. The normalization factor from missing coordinates contributes only exp(O_m(alpha/D)).

The stationary fraction is comparable to 1/alpha, so both neighboring ranks eventually lie in the valid central interval. On their 1/D neighborhood the second derivative of the log moment is O_m(alpha^2). Their relative rounding loss is exp[-O_m(alpha^2/D^2)]. This dominates all nonbulk competitors throughout the band, rather than only at sampled orders. The fixed initial compact interval covers the order-one crossing; if the lower bound already exceeds A0, that interval is empty and requires no separate argument.

## Method sharpness and integer rounding

The early vertex (m+1,1,...,1)/(D+m) has the exact moment in F24. Above c=1/log(m-1), its ratio to F_q diverges. Its antisymmetric Bell spike has tested partial-transpose expectation (1-m/2)/(D+m) < 0. The sharp coefficient therefore belongs to the relaxation method; it is not the actual APPT phase coefficient.

At the continuous stationary rank, direct differentiation gives g_q'' = -J_alpha, including the stated J_1. Third derivatives are bounded uniformly on every compact positive order interval. Taylor's formula holds for both neighboring integer ranks with an O(D^-3) remainder. Taking the smaller exact loss gives nearest-integer squared distance in the leading term. Near half-integers, cubic terms can change which exact rank wins, so the exact two-rank comparison remains necessary.

As an independent scope challenge, B_q(alpha)=O_m(alpha) near zero. The actual APPT one-hole state (I-P)/(D-1) has deficit log[D/(D-1)] ~ 1/D at every positive order. Its physical validity follows because the maximum eigenvalue of a pure-projector partial transpose is at most one. Taking alpha_D=D^-2 would therefore defeat bulk optimality eventually. The positive lower order bound is a real boundary, and the manuscript correctly keeps it.

## Supporting reading and computational limits

The ordinary predecessor EXACT_RECTANGULAR.md was completely read at its unchanged 165 lines. It already contains the same physical halfspace, vertices, projection membership, and sufficiently rectangular exact purity result. Only ENTROPY_ASYMPTOTIC.md 1–50 and 269–273, and SUBUNIT_ALL_DIMENSIONS.md 1–50, were read as continuous old scope passages. Their remaining proofs were not audited.

The primary [Ahiable–Kothakonda–Winter v2, Section 6.2](https://arxiv.org/html/2608.03390v2#S6.SS2) was independently read at rendered lines 881–995. Theorem 6.10 optimizes the inscribed polytope; its stationary rank equals D theta_1. The subsequent full-APPT comparisons are numerical observations in tested dimensions. The [Tran v1 outer entropy statement](https://arxiv.org/html/2609.18568v1#S3) was checked at rendered lines 304–326. Neither complete original paper nor the full exact-qubit proof was newly audited. These checks do not establish exhaustive priority.

The unchanged 221-line check_bulk.py was read but not rerun by this reviewer. Selected status/count/failure sections of the Windows report were inspected. It records one implementation, 40,745 finite vertices, 81,120 exact moment identities, 93 retained compact failures and eight retained below-ceiling logarithmic failures. Bell controls evaluate the derived actual-projector expectation formula; the script does not independently construct every partial-transpose matrix. Smaller-dimension failures, including at 0.9 sigma logD, are compatible with existential eventual thresholds. Passing samples do not give an effective D0 or certify the infinite proof.

No Lean, Lake or kernel replay was run. No Gaussian dirty contents, old formal-root source audit, submission, Release, DOI, commit or push was performed by this reviewer. Only REVIEW.json and REVIEW.md were written. The same APPT direction adds no independent major-conjecture count. Growing m, orders tending to zero without a lower bound, every finite dimension, smallest onset, ASEP bulk attainment and the physical optimizer transition remain outside the proven scope.
