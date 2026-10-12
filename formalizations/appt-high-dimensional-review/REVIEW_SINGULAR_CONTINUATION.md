# Independent review: the singular APPT locus and purity-ball sufficiency

These results were recovered from unpublished WSL sources. This review did not infer correctness from old successful summary files: the recovered input manifest was checked, all three modules were read, and a new fresh build and trust-zero replay preceded independent GitHub CI. No source was attributed a stronger scope than its statement.

## Mathematical chain

For every Hermitian complex matrix H on the actual product space, partial transpose preserves Hermiticity and the square trace: purity(H^Gamma)=purity(H). The entrywise proof explicitly reindexes all four indices, so it does not mistake trace preservation alone for square-trace preservation. The Hermitian premise is essential.

If purity(H)<=1, each real eigenvalue of H has square at most one, hence is at most one. Applying the actual spectral theorem gives I-H>=0. Unitary invariance of purity and the partial-transpose identity therefore give all-unitary PPT for I-H. This theorem does not assume H>=0. For an actual density A, purity(A)<=1 is already proved, so I-A is APPT as an unnormalized matrix; it has trace D-1, not trace one.

To derive the standard trace-one purity ball, put c=D-1>0 and H=I-cA. Exact noncommutative expansion and trace(A)=1 give purity(H)=D-2c+c^2 purity(A). The hypothesis purity(A)<=1/(D-1) yields purity(H)<=1. Thus cA=I-H is APPT, and scaling by the proved positive inverse of c gives APPT for A. The strict D>1 assumption is discharged rather than using totalized division at zero.

For a singular APPT density, the previously verified ordered rank-two inequality and trace normalization force the sorted spectrum to be D-1 copies of 1/(D-1) and one zero. Its exact second moment is 1/(D-1). Conversely any actual density with that spectrum lies in the proved purity ball. This proves the singular equivalence and the equivalent purity test without assuming an eigenbasis/unitary bridge in the final statement.

For actual attainment, a singleton coordinate projection Q is proved Hermitian, idempotent, positive and trace one. The matrix (I-Q)/(D-1) is an actual density and APPT; its diagonal form gives determinant zero by a vanishing product factor. The necessity theorem then also supplies its exact purity. This is not just existence of a list of real numbers.

## Controls and boundary of coverage

A 2x3 projection-family density has purity 11/50>1/5 and is APPT. It rejects necessity of the purity-ball condition without the singularity premise. The existing nilpotent regression rejects using Hermitian square-trace identities for arbitrary matrices; zero-dimensional, false-PPT/APPT, wrong local-dimension and denominator controls remain in the same kernel closure.

Independent run 38189500302 passed all stages. The full closure contains 42,271 declarations with 139 explicit roots; it is replayed from an empty kernel at trust level zero. Only the three standard allowed axioms occur. The singular equivalence is the primary forged-proof target; additional unchanged-type controls target the purity ball and singular attainment. All 65 source/configuration inputs match the exact tested commit. Logs, source comparisons and complete dependency lists are retained separately from development diagnostics.

The 10x38 counterexample has purity outside this ball and contains a joint projection-plus-spike term. It is not certified by these sufficient theorems. Matching growing-dimensional lower limits, exact rectangular optimization, entropy extrema and dimensional rigidity remain unclosed. Existing compactness and finite attainment do not prove any of those numerical or asymptotic claims. No publication or priority claim is made here.
