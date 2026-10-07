# Proof self-review and verification boundary

7 October 2026. This is a model-conducted self-review, not a separate mathematician's review.

## Independent all-orders theorem

1. The defect includes **all ordered contraction indices**. This makes the contraction-index action orthogonal under a change of basis; a small selected subset would not justify the invariance proof.
2. For even order, a negative absolute maximum is handled by changing the sign of the entire tensor. The decomposition class permits negative weights, so distance is unchanged.
3. The stationarity identity is X(v)v=lambda*v. The sphere Hessian gives mu <= lambda/(p-1), not an assumed gap between tensor weights.
4. The critical commutator entry is (mu_j-lambda)T(alpha,j,1). Its denominator has magnitude at least lambda/2 for every p >= 3. Negative mu are allowed. Aggregation counts both ordered commutators and both skew entries; their only row/column overlap is a zero self-commutator.
5. For k copies of index one, full symmetry gives the exact permutation fraction k(p-k)/(p(p-1)), at least 1/p. This remains true with repeated other indices. The exact checker tests the identity for each k. The estimate fails for unsymmetric tensors; no such extension is claimed.
6. The complementary commutator is a compression plus b_alpha b_beta^T-b_beta b_alpha^T. The direct-sum correction norm is bounded by sqrt(2) sum |b_alpha|².
7. The mixed-entry bound is homogeneous. The induction branches at lambda <= sqrt(2pmR), so no lower-weight condition is hidden. Grouping coefficient vectors in the polarization estimate and checking the explicit induction inequality give the polynomial constant (p^p/p!) sqrt(2p) m^(p/2). The cubic refinement gives 5 m^(3/2).
8. The zero-defect case is covered by the same induction. Dimension one is exact, including zero tensors.
9. The decomposition class is closed because bounded tensors have bounded projection weights and compact orthogonal bases. This validates the positive-distance sharpness witness.
10. Scaling the explicit noncommuting tensor yields optimal residual exponent for each m >= 2, p >= 3. The argument says nothing about best dimension constants.
11. The separate dimension obstruction uses harmonic binary forms in orthogonal blocks. Their ordered contraction parity counts give residual squared k*2^(2p-2). The diagonal maximum remains one, limiting every orthogonal basis's total projection energy to 2k and proving an unavoidable dimension^(1/4) lower growth. The exact checker verifies the norm and residual identities on selected orders.

## Cubic and binary refinements

The cubic splitting norm counts three permutations of every mixed coefficient. The binary tensor norm counts three copies of T112 and T122. The residual includes both ordered commutators, producing the factor four in R=4|A²-B²/9|. The harmonic witness has squared tensor norm four, squared distance three, and residual four. Exact polynomial checks and Lean verify the corresponding algebra.

## Nonlinear compatibility and conditional entropy

The first Taylor coefficient imposes input/output tensor compatibility, not merely symmetry of each matrix. The next coefficient forces commutators. The linearized kernel additionally uses diagonal normalization; its only remaining directions are rotations. The negative Sobolev target is defined as the dual of componentwise H0¹ on the unit ball. Compactness is used only to enter the coercive neighborhood; the local linear bound follows from the explicitly proved transverse derivative kernel.

Gaussian spectral calculus uses the Frobenius Lipschitz estimate, which need not be an operator-norm estimate. Distributional curls of weak Jacobians vanish. Gaussian Poincaré supplies the Wasserstein coupling, and covariance whitening introduces an orthogonal factor, which is absorbed into the minimization.

The entropy corollary is dependent on R and, for nonsmooth densities, the upstream approximation input. Scalar certificate replay verifies only the scalar part of that source. It is not a certification of its entire transport/entropy argument. No conditional statement is relabeled unconditional.

For truncated exponentials, actual entropy, mean and variance are calculated by integration. Both possible one-dimensional orthogonal orientations have a positive tail-cost bound. The obstruction covers nonsmooth log-concave densities and permits logarithmic improvements at exponent one half.

## Executed checks

The recorded finite checks use exact fractions and polynomial identities, remain active with optimization, and include missing-constraint or malformed-input controls. Lean 4.34.1 compiles seven algebraic exports with only the standard reported logical axioms. The PDF build checks warning conditions. These checks have sharply stated scope; neither finite tests nor these partial Lean exports replace the written general proofs.
