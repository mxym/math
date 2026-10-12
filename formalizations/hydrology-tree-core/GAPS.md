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

## 1. Exact algebraic multiplicities and resultant identity

The all-tree factorization is complete, but a displayed factorization does not
alone establish the exact multiplicity of each coordinate in the full polynomial.
Complete the polynomial divisibility/nondivisibility argument ruling out hidden
individual-rate factors in sibling resultants. A uniform all-tree zero-outward
construction with distinct inward rates is now proved, including an assignment
with any selected inward coordinate zero. This is a constructive boundary lemma,
not yet the full polynomial multiplicity theorem.

The exact signed resultant identity is now proved in AllTreeResultant, for
every real rate vector with a fixed tree-dependent sign. No zero-rate or
root-collision exceptions remain. Still state and prove the tree multiplicity
conjecture corollary with its original parameter convention and explicit
multivariate polynomial meaning.

## 2. Positive realization existence and exhaustive count

Uniqueness per prescribed recursive factor assignment is proved. Still required:
reciprocal Stieltjes pole/zero interlacing and residue signs; construction of a
positive physical model for every admissible recursive partition; completeness
of the assignments; the factorial fiber count and any global branch topology.
Distinct assignments need not give equal rates. Do not relabel assignment-wise
uniqueness as uniqueness from root observations alone.

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
