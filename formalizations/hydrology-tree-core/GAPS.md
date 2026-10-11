# Remaining mathematical obligations — not assumptions

The target remains the Jacobian of the actual characteristic/cofactor
coefficient map of a finite bidirected tree with one leak:

    det DC_T = ± product_v f_v^(n_v-1) a_v^n_v
      * product_(sibling pairs at every node) Res(P_v,P_w)^2.

## Completed proof-critical components

Actual matrix and rate-coordinate semantics; physical rate-coordinate Jacobian
at all real rates; exact actual characteristic/cofactor encoding and resolvent;
all-finite-block characteristic and cofactor attachment; arbitrary-branch matrix
assembly; actual physical last-leaf recurrence; all-arity coefficient gluing,
including its second-order regularity; monic numerator scaling and root-update
Jacobians; canonical root-branch partition and exact original matrix block
transport. None of these is supplied as an assumption in place of its proof.

## Full coefficient Jacobian induction

The actual child principal blocks are now identified with smaller OrderedTrees,
with rate-independent increasing enumeration, parent transport, conservation,
all matrix entries, and characteristic/root-cofactor polynomial equality proved.
The original exit-to-parent rate is retained as each child's single leak.

Still prove the complete input rate-coordinate permutation and finish the
induction with all child Jacobians, scaling, root update, chain rule and
orientation bookkeeping. Arbitrary external graph numberings and the
observation-root/leak-root distinction need their own reindexing statements.
A matrix-coordinate Jacobian is not the target coefficient Jacobian.

## Multiplicities and conjecture corollaries

After the full factorization, prove that sibling resultants have no additional
individual-rate factors. A displayed factorization alone does not prove the
exact coordinate multiplicities. Catenary and general-tree conjecture statements
must be derived with their actual published parameter conventions, not merely
matched by a finite example or name.

## Cancellation and positive singularities

Prove the complete resultant identity between the characteristic polynomial
and actual root cofactor, plus stability/symmetrization and the required spectral
and minimality statements. Do not conflate the original unreduced coefficient
map with a reduced transfer function: zero-rate response cancellation need not
make the unreduced coefficient Jacobian singular.

## Global positive realizations and fiber count

Prove rational Stieltjes pole/zero interlacing and residue signs, every step of
the constructive inverse, physical positivity and conservation, uniqueness for
a fixed recursive pole assignment, completeness of all positive realizations,
the factorial count and any claimed global continuity or analytic branch
classification. These do not follow from a nonzero local Jacobian or finite
rational realization fixtures.

No main theorem is exported with one of these missing conclusions as its own
hypothesis. No complete-formalization Release is justified yet.
