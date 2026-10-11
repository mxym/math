# Unresolved mathematical obligations

This package currently closes the two-polynomial gluing Jacobian, monic-scaling
Jacobian, and root polynomial coefficient-update Jacobian in actual real
coefficient spaces. Every derivative is a `HasFDerivAt`/`fderiv` statement.

The full target remains:

    det DC_T = ± product_v f_v^(n_v-1) a_v^n_v
      * product_(sibling pairs v,w at every node) Res(P_v,P_w)^2.

To obtain it, the arbitrary finite rooted tree, its actual rate matrix, its
characteristic polynomial and root cofactor must be constructed; the actual
Schur/determinant recursion must be proved; and the polynomial core must be
assembled with the physical rate-coordinate Jacobian and all-child induction.
A recursive polynomial definition alone is not that matrix identification.

The nonroot-leak version needs its orientation/reindexing and conservation
chart proof. Exact coordinate multiplicities require nondivisibility of every
sibling resultant by each individual rate coordinate, not just the displayed
product formula. The conjecture corollaries remain unexported until these
connections close.

The positive singular-locus theorem also requires the actual stability and
symmetrization theory, cancellation identity, and precise handling of reduced
versus unreduced transfer functions. A two-store zero-rate boundary can have
response cancellation while the unreduced coefficient Jacobian is nonsingular;
no theorem may erase this distinction.

The global positive-fiber classification additionally needs the rational
Stieltjes decomposition and sign/interlacing theorem, reconstruction of every
positive realization, uniqueness for a fixed recursive pole assignment, the
combinatorial count, and any claimed continuity/analyticity of inverse branches.
These are not proved by finite rational examples, nor by the local Jacobian.

No custom axiom, missing-theorem assumption or conditional wrapper presented as
the final theorem has been added. No full-formalization Release is justified.
