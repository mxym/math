# Remaining proof obligations — partial formalization

The principal unfinished target is the Jacobian of the actual characteristic /
root-cofactor coefficient map, for every finite physical tree:

    det DC_T = ± product_v f_v^(n_v-1) a_v^n_v
      * product_(sibling pairs at every node) Res(P_v,P_w)^2.

## Completed connections

Actual physical matrices, characteristic/cofactor encoding, conservation,
resolvent identities and the physical rate-coordinate Jacobian are proved.
Actual root-branch partition and complete block decomposition, increasing child
renumbering as a strictly smaller tree, retained exit-to-parent leak, all child
matrix entries and characteristic/cofactor equalities are proved. The exact
input-rate partition is a proved linear equivalence onto independent child data.
The nonlinear root coupling has an actual Frechet Jacobian equal to the product
of child leak parameters, including when those parameters are zero.

The end-to-end characteristic and root-cofactor recursions now apply directly
to the original OrderedTree, not merely to a separately assembled arrow model.
All-arity polynomial gluing, numerator equality, required second-order
regularity, monic scaling and root-update Jacobians are also proved.

## Full coefficient-Jacobian induction

Still assemble the determinant chain rule in compatible finite-dimensional
bases for the independent family of child rate data, their coefficient maps,
root coupling, numerator scaling, all-arity gluing and root update. Prove the
complete induction and its conversion to the displayed edge-exponent and
sibling-resultant formula. This assembly is not supplied as a hypothesis, nor
is the separately proved rate-coordinate Jacobian called the target Jacobian.
Basis orientations and arbitrary external graph relabelings need explicit
bookkeeping; the observation-root / nonroot-leak version also needs transport.

## Common-root classification versus remaining spectral/Jacobian claims

`physicalCommonRoot_iff_siblingCollision` now proves the entire all-size
classification of actual characteristic/cofactor common zeros: they occur iff
actual sibling principal-block polynomials share that value somewhere in the
tree. The result holds in every field extension of the reals, for nonzero
internal directed rates of either sign, and arbitrary root leak. The rate
inheritance, local cancellation algebra and full tree induction are proved.

Constructed diagonal symmetrization, positive energy, strictly negative real
characteristic roots, and normalized nonnegative-weight finite Stieltjes
root responses are now proved. These allow zero observation weights and
repeated characteristic roots. Still unproved: the global resultant identity
with the coefficient Jacobian, the equivalence to Jacobian singularity, and
a controllability/observability theorem about the underlying ODE system.
The common-root result must not be described as those unproved equivalences.
Zero internal rates are excluded in this classification; the full Jacobian
target is supposed to include them. Unreduced coefficient data are not silently
replaced by the cancelled response at a zero-rate boundary.

## Exact multiplicities and published conjectures

After the complete Jacobian factorization, prove that sibling resultants have
no extra individual-rate factors, and derive both conjecture statements with
their original rate conventions. The factorization alone is not exact
multiplicity, and finite examples are not all-size conjecture proofs.

## Global positive realizations and fiber count

Still prove rational Stieltjes interlacing and residue signs, the constructive
inverse, positivity / conservation, uniqueness for fixed recursive pole
assignments, completeness of every positive realization and the factorial
count. Any global analytic inverse-branch classification requires its own
proof. None follows from the local Jacobian or from the common-root theorem.

No complete-formalization Release or DOI is justified by this checkpoint.

## Endpoint path subcase now proved

For the actual endpoint-catenary coefficient map, the all-size determinant
induction and standard-coordinate normalization are now proved in
`catenary_standard_jacobian` and `catenary_standard_jacobian_sq`; the exact
zero-rate singular locus is `catenary_standard_singular_locus`. The sign is
fixed per size and has magnitude one, proved by bilinear coordinate-energy
preservation. This does not yet close the full branching-tree induction.
`PhysicalConstants` proves the exact characteristic/cofactor constants for
all rooted trees. The global branching-tree and realization gaps above remain.

The endpoint-path uniqueness part is now also proved:
`catenary_global_fiber_at_regular_point` identifies the entire REAL coefficient
fiber at every nonsingular path model, with no assumption on the competing
model. This is not the arbitrary-tree fiber count or realization-existence
theorem and not reduced-response uniqueness at cancellation boundaries.

Path coprimality and global identification from actual nonpole root resolvents
are now proved in CatenaryCoprime, assuming nonzero internal rates only for the
reference path. This is not arbitrary-tree Stieltjes realization existence or
global fiber counting. Positive-spectrum response weights need not all be
strictly positive until a further noncancellation argument is supplied.
