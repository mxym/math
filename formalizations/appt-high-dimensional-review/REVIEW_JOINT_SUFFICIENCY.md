# Independent review: joint APPT sufficiency and the physical counterexample

## Exact verified claim

For every finite first-factor index type a of cardinal m>=4 and every finite second-factor type b, let P be an actual complex matrix with P>=0 and I-P>=0. For an actual vector v with v* v=1, the matrix B=(2m-5)I+2P+4(m-4)|v><v| is APPT under every global unitary. The order structure on a only labels the proof's signed pairs; no spectral ordering assumption is made. The condition v in range(P) is needed to describe the three-level spectrum in the research notes but is not needed by the generic positivity bound.

For m=10,n=38, P projects onto the 147 coordinates satisfying 38*i+j<147, and v is the first coordinate vector. The normalized B/6018 is exactly diag(41,17[146],15[233])/6018. Its original complex trace-square is 2675/1006009, strictly greater than 97/36481 and 5/1881. These are the two displayed candidates in Ahiable--Kothakonda--Winter's arXiv:2608.03390 Theorem 6.3 and Conjecture 6.7, evaluated at these dimensions. Attribution to the source paper is separate from Lean's explicit numerical-formula statement: its entire polytope theorem is not imported as a formal assumption or claimed as independently formalized here.

## Claim-to-proof dependency map

| Mathematical obligation | Modules / checked endpoints |
|---|---|
| Orthogonalize coefficient rows via the genuine spectral theorem | SchmidtRows: exists_unitary_orthogonal_rows, gram_zero_row |
| Reconstruct normalized rows including zero singular values | SchmidtNormalize: exists_schmidt_rows, normalizeRows_reconstruct, normalizeRows_gram |
| Rectangular contraction frame on the actual product space | SchmidtFrame: schmidtFrame_gram, schmidtFrame_contraction |
| Actual partial transpose equals a weighted exchange congruence | SchmidtPartialTranspose: partialTranspose_rowPure_eq_schmidt |
| All positive and negative pair entries simultaneously diagonalized | SchmidtDiagonal: schmidtExchange_diagonalization, schmidtSigned_add_negative_nonneg |
| Trace duality, compression and diagonal lower bounds | QuantumTrace; SchmidtModel: trace_contraction_diagonal_lower |
| Joint scalar SOS for every pair, not a supplied largest pair | SchmidtMass; SchmidtJointScalar: schmidt_joint_pair_nonneg, schmidt_joint_signed_nonneg |
| Arbitrary, unnormalized complex test vector, including zero | SchmidtJointWitness: exists_pure_signed_model, pure_joint_witness |
| Complete quadratic-form and all-unitary conclusion | JointSufficiency: jointSpike_partialTranspose_posSemidef, jointSpike_absolutelyPPT |
| Original 380-dimensional matrix, density, exact entries and purity gap | Counterexample1038: counterexample1038_refutes_formula |

For each test x, the construction provides the same s,L for W=(|x><x|)^Gamma=L diag(d)L*, with L a contraction and sum(s_i^2)=||x||^2. Put N=sum_{i<j}s_i*s_j and c=(2m-5)||x||^2-2N. Compression proves Tr(PW)>=-N. The SOS proves c>=0 and c+4(m-4)d_i>=0 for every signed entry. Therefore cI+4(m-4)W>=0. Testing this on the normalized v and using trace duality establishes x*B^Gamma*x>=0. All imaginary-part and Hermitian obligations are discharged, not replaced with a real surrogate. Unitary transport proves the full orbit statement.

## Verification and limitations

All mathematical modules in this chain compiled locally in WSL. The independent source-bound CI then freshly rebuilt the complete integrated package and replayed its transitive closure in an empty trust-zero kernel. Successful sources are on the clean branch review/appt-joint-sufficiency; literal evidence is bound to c7bd84ed and run 38200910959. The old research notes, qutrit completion proof, and immutable releases were not altered.

The primary and additional forged-proof tests target the actual final objects and quantifiers. No sorry, custom axiom or untrusted native_decide is used. The result is not the unrestricted APPT purity maximum, a minimal-dimension classification, or a proof of absolute separability. The later asymptotic/entropy/rigidity claims retain their own unclosed dependencies in COVERAGE.md.

## Source-transport failure and repair

A Windows no-checkout worktree initially had an uninitialized index. An isolated transport branch therefore recorded unintended repository deletions, despite the intended proof files matching the compiled WSL bytes. This branch was never merged or pushed to main. The exact twelve proof modules and three integration files were extracted into a clean VPS worktree based on current main; all 79 pins and an explicit staged allowlist were checked, with no deleted files, before the clean c7bd84ed commit and independent verification.

The temporary branch was repaired by a non-forced forward commit 8426d5ecd053607a7757e1dab84eaf36f0fff997 restoring the full repository tree. Its final tree matches the clean proof tree 3fe12de560cfa918f6b5b777b419dbc008a5f639. Its erroneous ancestry is not merged into main. Transport receipts and failed compiler trials are not used as proof certificates. Future sparse transport must initialize the index from the base tree and reject every unexpected staged path before committing.

## Fully quantified formula and robustness checkpoint

The later source c129497b and independent run 38202563748 add JointControls, JointRobust and JointBoundaryControl. The formula definition uses natural-number ceiling `((m-1)*n+1)/2`, and the final negated statement ranges over all dimensions and all actual APPT densities in the conjectured domain. The positive witness remains the original matrix, not a surrogate with larger assumptions.

Adding exactly 1/1000 white noise preserves a strict purity-formula violation and gives the literal all-unitary matrix floor I/380000. The failing-coefficient control instead changes 24 to 25 in the negative-pair boundary layout; it is proved density and non-APPT. A scalar test takes s=(4,4,1,...,1), producing 0 for coefficient24 and -16 for coefficient25. Its separate physical proof applies the rectangular necessary witness and derives a negative quadratic form from the actual defined matrix.

All new declarations were compiled before the separate independent workflow; all original proof roots and corruption controls were retained. The final closure, extra controls, source bytes and original logs were checked again after download. These results do not automatically certify the infinite counterexample families' remaining parameter arithmetic, the growing-dimension lower limits, the full entropy counterexamples/minima, or dimensional rigidity. No further preprint or Release was prepared.

For source transfer, a corrected three-file sparse transport initialized the complete base index with `git read-tree HEAD` and explicitly rejected any unexpected staged path or deletion. Windows networking subsequently failed, so the same three locally compiled sources were transferred through a SHA-256 checked archive: c0987690259190153f6ca7cb71a54a622df18633249260701f3fad1bea29baa1. Every extracted Lean source matched its own recorded compiler hash before integration. No transfer receipt was treated as kernel verification.
