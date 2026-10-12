# Hydrological tree identifiability — partial overall Lean formalization

The all-size, all-real-rate Jacobian factorization for the actual rooted tree
coefficient map, its exact signed characteristic/cofactor resultant identity,
and all exact multivariate coordinate multiplicities are now proved in Lean.
The overall program remains **PARTIAL**: positive-realization existence and
exhaustive fiber count, and the remaining graph-presentation, leak-location
and ODE bridges still need proofs. See `GAPS.md`.

## Main theorem: arbitrary branching, actual physical objects

`HydrologyTree.full_tree_standard_jacobian` states, for every finite OrderedTree
T, a fixed sign epsilon in {1,-1}, independent of all rates, such that

    det D C_T = epsilon * product_(edges v) a_v^N_v f_v^(N_v-1)
      * product_(vertices u) product_(sibling pairs v<w at u) Res(P_v,P_w)^2.

Here C_T reads the non-leading coefficients of the actual conservative
compartment matrix's characteristic polynomial and original root principal
cofactor. N_v is the size of its actual rooted principal subtree; P_v is the
actual subtree characteristic polynomial, retaining its exit-to-parent rate
in the original diagonal. All definitions and the actual Frechet derivative
are included. Zero rates, zero root leak, repeated roots and zero resultants
are not excluded. The sign is proved to be exactly ±1, not an unspecified
nonzero normalization, and the factors are expressed on the original edge and
vertex sets. The one-vertex case is included.

Proof chain: genuine child-tree/rate extraction and independent parameter
permutations; actual all-child determinant/cofactor recursion; all-arity monic
scaling, gluing and root update; coefficient-dot-preserving transformations;
complete Frechet chain rule; strong induction; original-coordinate products.

Main entry: `import HydrologyTree`. Supporting entries include
`all_tree_canonical_jacobian`, `treeCanonicalJacobian_recurrence`, and
`differentiable_physicalCoefficientMap`. The recurrence's smaller-child
hypotheses are discharged by the final induction, not passed to the main theorem.

## Consequences proved without a hidden spectral input

`treeJacobian_ne_zero_iff_coprime` gives the complete regularity criterion at
nonzero-edge real references. `positive_tree_jacobian_zero_iff_collision`
identifies the singular set of positive internal-rate models with actual sibling
spectral collisions somewhere in the tree. `positive_tree_jacobian_iff_full_modes`
adds the equivalent full distinct positive Stieltjes-mode characterization when
the root leak is positive. Grounded energy, detailed balance, negative-real
spectrum and normalized physical Stieltjes polynomials were proved separately
and are genuine dependencies, not assumptions.

`regular_tree_assignment_unique` gives at most one real rate vector per
prescribed recursive subtree characteristic assignment at a regular nonzero-edge
reference. The competing rates need not be positive. This is not the still-open
existence or count of every such assignment.

`zero_outward_characteristic` and `zero_coordinate_coprime_witness` provide an
all-tree exact triangular boundary construction for the remaining hidden-factor
analysis. No finite numerical fixture substitutes for these universal results.

The earlier all-size endpoint-catenary Jacobian, its zero-boundary singular set,
global real-rate coefficient uniqueness, and noncancelling root-resolvent
identification remain included. The actual physical matrix, conservation,
rate-coordinate Jacobian, child principal blocks and full coefficient encoding
are reused, not replaced by surrogate recursively assumed polynomials.

## Verification and reproduction

Fixed Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; all transitive dependencies are pinned.

    bash fetch_cache.sh
    python3 reproduce.py --output-dir /tmp/tree-proof-independent-check

The output directory must be new. The script checks every proof-input hash,
constructs a fresh Lake source tree with zero owned objects, builds it, separately
compiles every owned module, audits roots, and replays the used declaration
closure into an empty trust-level-zero kernel. It compares root types and
universes and allows only propext, Classical.choice and Quot.sound. Deliberately
false source mutations must fail. Complete logs and a deterministic source
archive are retained; old logs do not certify new source changes.

This extension compiled in the isolated WSL development environment. Its final
source-bound independent verification is a separate GitHub Actions run. The
previous independent checkpoint is c9161c28: 77 modules, 693 roots, 43,053
replayed declarations, 32 rejected controls. Its original evidence is under
`verification/hydrology-tree-core-c9161c28` at the repository root. Consult the
new checkpoint's own receipt for the expanded verification scope.

No custom mathematical axiom, unproved main-theorem interface, sorry, admit,
native_decide or unsafe mathematical dependency is allowed. Development compiler
sessions are diagnostics, not independent proof certificates or human peer review.

## Provenance

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. No external funding; AI-assisted development.
Existing repository and third-party notices remain in force. Original additions
retain all rights not otherwise granted by an applicable existing license.
No historical-priority or complete-program claim, completion Release or DOI is
made by this partial-overall package.

## Exact signed resultant identity

`full_tree_resultant_jacobian` now proves, for one sign ε depending only on
T and its fixed coordinate conventions, simultaneously for ALL real rates,

    Res(P_T,F_T) = ε * (product_e f_e) * det D C_T.

P_T and F_T are the actual characteristic and root principal-cofactor
polynomials and D C_T is the actual standard-basis Frechet Jacobian. Zero
rates, zero root leak, repeated roots and zero resultants are included.
`physicalResultant_eq_signed_jacobian` gives the explicitly defined sign;
`physicalResultant_jacobian_square` is its exact sign-independent consequence.
The proof establishes actual-degree resultant algebra, arbitrary-family signs,
finite numerator enumeration, the physical root recursion, and strong induction.
It does not divide by an edge rate or use only a generic-parameter argument.

This extension has compiled; its independent source-bound verification is the
new run for its own commit. The preceding all-tree checkpoint 2684e3b3 passed:
95 modules, 860 roots, 43,356 empty-kernel replay declarations, and 36 rejected
mutations. That old receipt does not certify the new resultant extension.

## Exact algebraic multiplicities — not just boundary evaluations

`RingTreeModel` constructs the same edge-conservative physical matrix over
arbitrary commutative coefficient rings and proves its specialization to the
actual real model. `RingSiblingResidual` builds the actual monic subtree
resultant residual over independent multivariate rate variables and proves
that all real specializations give the physical residual.

`SymbolicTreeJacobian` constructs a multivariate polynomial whose evaluation
at EVERY real rate vector equals the actual standard-basis Frechet Jacobian.
It proves that this polynomial is the UNIQUE polynomial with those evaluations.
Uniform coordinate-hyperplane witnesses then prove that no individual rate
variable divides the residual polynomial. No finite specialization test or
unproved polynomial-representation premise substitutes for this bridge.

`TreeExactMultiplicities` proves, in the multivariate polynomial ring itself,

    multiplicity(a_e, J_T) = subtreeVertexCount(e),
    multiplicity(f_e, J_T) = subtreeVertexCount(e)-1.

Equivalently, exactly the displayed power divides J_T and the next power does
not. The root-leak variable does not divide J_T. The existence-and-exact-powers
theorem constructs its polynomial, with no representation or multiplicity
assumption. The explicit determinant of formal partial derivatives of the actual symbolic
coefficient polynomials is now also proved equal to this unique polynomial;
see `FormalTreePolynomial` and the mathematical statement in `FORMAL_THEOREMS.md`.

`TreeBoundarySingularSet` gives the full real Jacobian singular set, including
zero-rate boundaries: a zero inward rate, or a zero outward rate whose subtree
has more than one vertex, or failure of sibling coprimality. `ResultantBoundary`
proves that actual characteristic/cofactor coprimality is equivalent to ALL
outward rates nonzero AND the Jacobian nonzero; a leaf outward-zero cancellation
must not be confused with a singular unreduced coefficient Jacobian.

The signed-resultant checkpoint 637a50fc passed independent run 38212403838:
100 modules, 897 roots, 43,475 empty-kernel declarations, and 38 rejected negative
controls. The new multiplicity/boundary extension receives its own separate
source-bound verification; the earlier receipt does not certify these new bytes.

## Formal partial-derivative determinant

`MultivariateDifferential` proves the Frechet derivative of arbitrary finite
multivariate polynomial evaluation from formal partial derivatives.
`PolynomialMapJacobian` identifies the determinant of this formal derivative
matrix with the actual Frechet determinant. `SymbolicCoefficients` constructs
the actual physical matrix characteristic/cofactor coefficient polynomials.

`formalTreeJacobian` is defined as the determinant of their formal partial
derivatives, independently of the factorization. `formalTreeJacobian_evaluate`
proves equality to the actual standard-coordinate physical Jacobian at every
real rate vector. `formalTreeJacobian_factorization`,
`formalTreeJacobian_exact_powers`, and the inward/outward multiplicity theorems
complete the algebraic proof for this independently defined formal determinant.
`catenary_standard_formal_polynomial` gives its all-size endpoint-path monomial.

The source has compiled and its full source-bound independent verification is
the new run for this exact checkpoint. Earlier 100/110-module receipts must not
be reported as certifying the additional formal-derivative files.

## Constructive reciprocal Stieltjes transformation

`exists_positive_reciprocal_stieltjes_data` proves the full reciprocal
transformation from any normalized strictly positive finite Stieltjes sum with
strictly increasing positive rates. Actual numerator zeros exist strictly between
every consecutive pair of poles, factor the entire numerator and are all simple.
Their reciprocal residues are proved positive from the actual derivative identity.
The reciprocal polynomial identity follows from checked monic division and
interpolation. The new root-leak value is the original reciprocal at zero and is
strictly positive. The one-store/empty-zero case is included.

`exists_positive_reciprocal_data_unordered` removes the sorted-label restriction
by a proved finite sorting permutation and exact reindexing of both polynomials.
`StieltjesGrouping` proves the numerator/denominator regrouping needed for every
labelled child-pole allocation. These results use real IVT, polynomial degree
and derivative theorems; no external Stieltjes theorem or root solver is assumed.

Positive realization of every full tree and exhaustive factorial counting remain
separate tasks. The new transformation source compiled; its independent source-
bound CI receipt is distinct from the earlier verified algebraic checkpoints.
