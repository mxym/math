# Exact remaining obligations — partial overall formalization

## Completed at the current source checkpoint

The arbitrary-branching coefficient-Jacobian induction is now proved for every
finite topologically numbered rooted tree and every real rate vector, including
zero rates, repeated roots and a zero root leak. It is the derivative of the
ACTUAL characteristic/root-cofactor coefficient map in standard ascending
coefficient bases, not the easier rate-to-matrix coordinate Jacobian.

`full_tree_standard_jacobian` proves a sign depending only on the tree and
coordinate order, valid simultaneously for all rates. Its rate exponents are
the sizes of the actual recursively extracted principal subtrees; its sibling
resultants are computed from the actual physical subtree characteristic
polynomials. The proof includes child independence, actual coefficient
semantics, the global Frechet chain rule, determinant normalization and original
vertex/edge product flattening. No main conclusion is supplied as a premise.

For nonzero real internal rates, Jacobian regularity is equivalent to coprimality
at every actual sibling family. For positive internal rates it is equivalent to
absence of real sibling spectral collisions and actual polynomial cancellation.
With a positive root leak, it is also equivalent to full distinct positive
Stieltjes modes. These are now actual Jacobian equivalences; ODE claims remain
separate. Rate uniqueness per prescribed recursive factor assignment is proved.

## 1. Completed algebraic multiplicities and resultant identity

The exact all-rate signed identity Res(P_T,F_T)=epsilon*(product outward)*J_T
is proved, with a single tree-dependent sign for all rate vectors. The full
real-rate boundary zero-set distinction is also proved.

The complete sibling residual is now an explicit multivariate polynomial built
from ring-valued physical matrices; its specialization identity is proved.
The unique polynomial representing the actual Frechet Jacobian exists, and
its individual-rate multiplicities are proved EXACTLY by polynomial prime
factor/divisibility arguments and uniform hyperplane witnesses. The next power
is excluded, including the outward-leaf exponent-zero case and the root leak.
These algebraic multiplicity obligations are no longer missing.

`formalTreeJacobian` now independently constructs the determinant of the matrix
of formal partial derivatives of the actual symbolic characteristic/cofactor
coefficients. Its evaluation is proved equal to the actual Frechet Jacobian,
and its exact polynomial factorization and multiplicities are proved. Thus the
explicit formal-differentiation interface is also closed. The endpoint path has
a separate all-size formal polynomial monomial theorem with the original
inward/outward exponents.

The independent graph-presentation and nonroot-leak conventions still require
the transports specified below; they are not hidden in this rooted-parent model.

## 2. Complete unrestricted-real full-response classification and counting

This block is now closed for the original OrderedTree model with a root leak.
`positiveReciprocalFiberEquiv` proves the exhaustive root-level actual-parameter
bijection. `positiveStieltjesRecursiveEquiv` recursively constructs the full
bijection with `RecursivePoleAllocations t`, a type depending only on the tree.
`positive_stieltjes_fiber_exact_card` proves finite cardinality exactly
n! / product_(v != root) |T_v| for a tree with n+1 vertices, with original labels
and actual subtree sizes. All inductive realization and counting premises are
discharged. No finite candidate list or external root solver is assumed.

`positive_root_response_fiber_exact_card` proves the same count for actual root
resolvent equality on its genuine nonpole domain, not an artificially stronger
observation of both coefficient polynomials. Every positive fiber member's actual
Jacobian is proved nonzero. Singleton trees and all labelled branch shapes are
included; coincident reference poles and targets with fewer than n+1 modes are
outside this enumeration theorem, not silently covered.

`real_stieltjes_realization_is_positive` additionally proves that EVERY real
rate vector with the full positive target pair is automatically strictly positive.
The competitor is not assumed positive, nonzero, stable or Jacobian-regular.
Monic child factors divide the simple split root cofactor; pure polynomial
splitting replaces any positivity assumption in the reverse factor extraction.
The actual child numerators are recovered by comparison with a proved positive
reference, and strong induction forces positivity at every descendant.

`realResponseRecursiveEquiv` gives the full bijection for ALL real root-response
realizations, and `real_root_response_fiber_exact_card` proves their finite exact
factorial count. `real_full_response_forces_positive_regular` proves both strict
positivity and the nonzero actual Jacobian, with neither assumed. Thus no extra
mixed-sign, zero-rate or singular real solutions are excluded from the count.
Complex-rate fibers have not been claimed or formalized.

These new files have compiled in the source-isolated development environment.
Their independent verification is tied to this new checkpoint's own source
hashes and CI receipt; earlier successful receipts do not certify new bytes.

## 3. Other tree presentations and leak locations

The main theorem uses the repository's actual OrderedTree encoding: every
nonroot vertex has one strictly lower-numbered parent. Transport to independently
presented arbitrary finite rooted graph objects needs an explicit enumeration
and coefficient/rate reindexing theorem. The non-observed-root leak version also
needs its observation-root versus leak-root coordinate argument. These variants
are not silently included in the proved rooted-parent statement.

## 4. ODE/system interpretation

The actual discharge-transfer bridge is now proved in DischargeFiber: root
leak times root resolvent, recovery of the unknown leak from discharge equality,
and equality of the unrestricted real root-response/discharge fibers with the
same exact finite cardinality. This removes any assumption that the physical
root leak is separately measured. It does NOT by itself prove the ODE claims.


The forward actual ODE bridge is now proved: global classical existence and
uniqueness for every positive physical model and continuous input, arbitrary
initial states, exact zero-initial root output, all-continuous-input discharge
equality for full-response-equivalent real models, and differential/integrated
storage balance. Positivity is proved from the full target response before this
ODE theorem is applied. The modal witness is actually constructed.

Still prove the reverse implication from all-input time-domain equality to
transfer equality, and the actual controllability/observability statements.
Piecewise-continuous or merely measurable forcing is not silently included in
the continuous-input theorem. Graph and alternate-leak variants remain separate.

Every independent receipt certifies only its own source bytes. No completion
Release or DOI for the entire research program is justified by this checkpoint.
