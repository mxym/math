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

## 2. Completed positive existence; exhaustive count remains

Reciprocal interlacing, complete zero factorization, simple roots, positive
residues and exact reciprocal reconstruction are proved, including the one-store
case and arbitrary input pole order. `positive_tree_stieltjes_realization_exists`
now also constructs an actual strictly positive rate vector on EVERY original
finite tree with the requested complete characteristic/cofactor pair. The proof
discharges all smaller-child existence obligations by strong induction. Same-size
topology non-identifiability is an exact corollary for positive full responses.

Root-level extraction of the unique labelled allocation from EVERY actual
positive model is now proved, as is the exact finite allocation count.
Still construct the EXHAUSTIVE bijection between each actual positive rate fiber
and all allowed recursive labelled pole allocations, and prove its factorial
cardinality. Existence on each tree and uniqueness for a prescribed assignment
are not an enumeration theorem. This remaining counting/classification obligation
is not supplied as a hypothesis to any completed theorem.

## 3. Other tree presentations and leak locations

The main theorem uses the repository's actual OrderedTree encoding: every
nonroot vertex has one strictly lower-numbered parent. Transport to independently
presented arbitrary finite rooted graph objects needs an explicit enumeration
and coefficient/rate reindexing theorem. The non-observed-root leak version also
needs its observation-root versus leak-root coordinate argument. These variants
are not silently included in the proved rooted-parent statement.

## 4. ODE/system interpretation

Controllability, observability and all-input equality of actual ODE solutions
need their definitions and state-space bridges. The proved matrix resolvent,
noncancellation and full-mode formulas do not themselves supply those bridges.

Every independent receipt certifies only its own source bytes. No completion
Release or DOI for the entire research program is justified by this checkpoint.
