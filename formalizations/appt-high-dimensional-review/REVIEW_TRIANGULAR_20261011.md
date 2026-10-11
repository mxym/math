# Physical paired-gap bound and triangular graph review

This checkpoint proves, for every actual complex APPT density matrix on C^m tensor C^n with 2<=m<=n,

    sum_(i=1)^R (lambda_i-lambda_(D+1-i))^2 <= 8*b^2,
    D=mn, R=m(m-1)/2, b=lambda_(D-m(m+1)/2+1).

The eigenvalues are canonically sorted. `density_appt_pair_gap_square_sum` assumes only dimensions, density and all-global-unitary APPT. The edge count and pivot are identified exactly by `upperPair_card_formula` and `pairedPivot_paper_index`.

`appt_all_ordered_pair_witnesses` constructs a single physical unitary for every bijection of paired gaps to upper-triangular edges. Disjoint diagonal, negative and positive eigenvalue slots are proved, not supplied. `appt_ordered_gap_square_bound` gives the squared action bound for every real vector and arrangement. Nonnegative entries turn the upper spectral cap into a two-sided cap, and the product of commuting positive matrices proves the square estimate. All imported matrix-order and functional-calculus dependencies belong to the replayed proof closure.

`triangular_degree_square` proves the decreasing row-by-row degree estimate in arbitrary dimension. A distinct order type `RowPair` preserves the ordinary product order and supplies the canonical enumeration. A star test controls the first row; the triangle estimate controls all other rows. The exact edge sum then gives the bound for actual ordered eigenvalues.

Regression theorems show that a negative-entry matrix can satisfy the one-sided PSD cap while violating the square bound, and an unordered late-edge graph violates the triangular inequality. The prior actual PPT-versus-APPT and sharp dimension-constant regressions remain audited.

The local fresh build, regressions and trust-zero replay completed: 41,929 declarations and 45 roots. Replacing the proof of the new physical paired-gap root by True.intro, without changing its type, was rejected. The 42-input SHA-256 manifest is d6100d3f52949553fce41fd727fd296fd4bc24117d1235bb7305fe0faf0ddb3c. The local kernel log hash is 5f56fdb91f164ef601236b3877dcf4d1b61212774b1e3440156e1553561cf336.

A Windows Git network failure prevented pushing local commit 4a032f592fa975571663eae18d4f0a4efca86d5c. The eight new modules were transferred with verified SHA-256 bindings; the aggregate, regressions and audit were reconstructed from the exact local diff. The entire resulting 42-input manifest matched the local audited manifest byte-for-byte before publication. This is a transport recovery, not a modification of the proof or weakening of verification. An independent remote replay is required before recording CI success for the new published commit.

Still missing: the baseline-sensitive refinement, the complete centered variance and normalization assembly, exact rectangular upper optimization/equality, joint projection-plus-spike sufficiency for the three-level counterexample, multiscale compactness and matching families, uniform extrema and asymptotic rigidity. No full high-dimensional purity/entropy theorem, new preprint or Release is claimed here.
