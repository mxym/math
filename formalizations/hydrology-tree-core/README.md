# Hydrological tree identifiability — partial Lean formalization

**PARTIAL FORMALIZATION.** The full all-tree characteristic/cofactor coefficient
Jacobian, exact rate-factor multiplicities, conjecture corollaries, positive
singular-locus classification and global realization/fiber enumeration are
not yet theorems of this package. No missing result is supplied as an axiom or
hidden main-theorem premise.

## Actual objects and completed proof components

The development uses actual finite parent-encoded rooted trees, edge-conservative
compartment matrices, characteristic polynomials and root cofactors, bounded real
polynomial coefficient spaces, and actual `HasFDerivAt` / `fderiv` derivatives.
No finite sample checker substitutes for the universally quantified proofs.

### Physical rates, matrix semantics and root decomposition

`RateChart`, `CompartmentMatrix`, `PhysicalBridge`, and `Resolvent` construct the
physical model and prove its water conservation, actual rate entries, diagonal
formula, coefficient encoding and root inverse-entry semantics. The true matrix
coordinate Jacobian is

    det D(rates -> (-A_vv, A_parent,child A_child,parent)) = product_e a_e.

It holds for every topologically numbered finite rooted tree and all real rates,
including zero rates. The genuine inverse identities require a nonzero
characteristic evaluation; the totalized inverse at a pole is not interpreted
as a physical response.

`RootBranches` constructs a rate-independent bijection from the original vertex
set to the root and its actual descendant branches. `BranchMatrixSupport`
proves that distinct branches have zero cross-transfers and meet the root only
at their branch roots. `PhysicalRootDecomposition` proves equality of the
reindexed actual compartment matrix with its root/branch block matrix, without
assuming any block decomposition. Original boundary-exit diagonals are retained.

`PhysicalLeaf` independently proves the exact last-leaf characteristic recurrence
for every original OrderedTree with an edge. Both structural sparsity and the
matrix-coordinate substitutions are proved, including zero-rate cases.

### Actual determinant and cofactor recursions

`EdgeDeterminant`, `EdgeCharacteristic`, and `RootAttachment` prove

    charpoly(edgeJoin A B) = charpoly(A) charpoly(B)
      - a*f * rootCofactor(A) rootCofactor(B),
    rootCofactor(edgeJoin A B) = rootCofactor(A) charpoly(B).

These are identities of actual matrix characteristic polynomials and adjugates,
with arbitrary finite block sizes and all real entries. The Schur calculation
away from finitely many roots is extended by a proved polynomial identity; no
spectral exception, positive-rate or coprimality assumption remains.

`BranchAssembly` proves the full characteristic and root-cofactor formulas for
every finite list of attached matrix branches, including the empty family.

### Actual all-arity polynomial Jacobians

`FamilyGluing` proves that the coefficient map

    (P_i; R_i) -> (product_i P_i; sum_i R_i product_(j != i) P_j)

has Jacobian equal to the square of the pairwise resultant product, for every
finite list of monic factor degrees and arbitrary strict-degree numerators.
Zero-degree factors, repeated roots, zero resultants and the empty family are
included. The numerator is an actual polynomial and its agreement with the
product derivative is proved. Second-order regularity is proved from the product
map, rather than introduced as a Hessian assumption.

The supporting `ProductDerivative`, `JacobianComposition`, `FamilyProduct`,
`FamilyResultants`, `FamilySmoothness` and `TangentJacobian` modules record the
complete derivative, basis-reindexing, determinant and regularity chain.
`Gluing` retains the separate two-factor proof. `Scaling` proves the exact
monic-scaling factor c^n including c=0. `RootUpdate` proves the actual root
coefficient-map Jacobian (-1)^n, monicity, exact degree and reconstruction.

Main aggregate entry: `HydrologyTree.lean`.

## Precise remaining connection

Root/branch matrix decomposition and arbitrary-family polynomial gluing are now
proved. The complete induction still needs the branch's rate-preserving
renumbering as a smaller OrderedTree, assembly of the child coefficient
Jacobians with scaling and root update, and all determinant chain-rule and
orientation bookkeeping. A matrix-coordinate Jacobian is not the full
characteristic/cofactor coefficient-map Jacobian.

The exact multiplicity, cancellation, positive spectral and global Stieltjes
realization/fiber proofs remain separately required. `GAPS.md` and
`DEPENDENCY_MAP.md` give the theorem-by-theorem obligations.

## Reproduction and verification

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, with every transitive Git
revision and relevant source blob checked against `lake-manifest.json`.

    bash fetch_cache.sh
    python3 reproduce.py --output-dir /tmp/tree-proof-independent-check

The output directory must not exist. The script constructs a fresh Lake source
tree with zero owned objects, builds it, separately recompiles every owned
module, audits all declared roots and replays the entire used declaration
closure into `mkEmptyEnvironment 0`. Root types and universes are compared.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Deliberately
false source mutations must be rejected by actual Lean compilation. Source
hashes are checked before and after; complete literal logs and a deterministic
verified-source archive are produced.

Completed independent checkpoints are source-specific:

- `37cc417b`, run 38145415740: 8 modules, 92 roots, 26,477 replayed declarations;
  six rejected mutations. Original artifact under `evidence/scaling-root-ci`.
- `d74acc4c`, run 38149404025: 12 modules, 149 roots, 27,668 declarations;
  eight rejected mutations. Original artifact under `evidence/physical-ci`.
- `a7e82785`, run 38150289891: 16 modules, 183 roots, 28,338 declarations;
  ten rejected mutations. Source-specific receipt in
  `../../verification/hydrology-tree-core-a7e82785/README.md`.
- `8de83755`, run 38152132585: 25 modules, 252 roots, 36,434 declarations;
  twelve rejected mutations. Original artifact under `evidence/family-ci`.

The root-partition extension is checked by its own subsequent independent
source-bound report; the 25-module receipt is not presented as its verification.
Development compiler diagnostics are not independent kernel certificates.

## Provenance

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. No external funding; AI-assisted development.
Existing repository and third-party notices remain in force. Original additions
retain all rights not otherwise granted by an applicable existing license.
No completion Release, DOI, external peer review, or historical-priority claim
is made for this partial package.

## Child principal blocks: completed identification

`ChildTree` constructs the increasing enumeration of each real root branch as a
strictly smaller OrderedTree and proves parent transport. `ChildRates` extracts
the actual rates, retaining the inward edge to the original root as the child's
sole leak. `BranchConservation` proves conservation of the actual principal
block and all reindexed column sums. `ChildMatrix` proves full matrix equality
(including diagonal entries), then equality of the actual characteristic and
root-cofactor polynomials. All rates are unrestricted reals, including zero.

Main new entries: `physicalBranch_eq_childTree`, `physicalBranch_charpoly_eq`,
`physicalBranch_cofactor_eq`, `childEdgeCount_lt`. The former child-renumbering
gap is closed. The full parameter permutation, global coefficient-Jacobian
induction, exact multiplicities and global classification still remain.

These five modules compiled in the local isolated Lean 4.34.1 environment.
Independent CI for this new source checkpoint is separate from older receipts.

## Global common-root theorem and complete physical recursion

The new main entry `physicalCommonRoot_iff_siblingCollision` is an **all-size
classification** for the actual physical tree polynomials, not a finite fixture:

    P_T(z) = F_T(z) = 0  iff  some actual sibling subtrees share the root z.

The field containing z can be any field extension of the reals. Every internal
directed rate must be nonzero, but its sign and the original root leak are
unrestricted. Each recursively visited block is proved to be the genuine
principal child matrix with its original boundary-exit diagonal retained.
`FiniteCancellation`, `PhysicalCancellation` and `TreeCancellation` prove the
local algebra, inheritance of nonzero internal rates and full tree induction.
This proves common-root cancellation, NOT its still-unproved equivalence to
coefficient-Jacobian singularity or the full positive-realization classification.

`ChildIndex` and `RateCoordinates` prove the exact rate-independent linear
isomorphism between original rate parameters and arbitrary independent child
data plus root/connector parameters. `RootCoupling` and `CouplingSemantics`
prove its nonlinear follow-up's actual Frechet derivative and determinant,
including zero child leaks. `DependentBlocks`, `ArrowDeterminant`,
`ArrowCharacteristic`, and `PhysicalRecursion` prove the end-to-end characteristic
and cofactor recursions of the original physical tree. No block recursion is
left as a premise at the common-root theorem's entry point.

The full coefficient-Jacobian determinant induction still needs to assemble
these actual maps in compatible bases. Exact factor multiplicities,
Jacobian/spectral equivalences and the complete Stieltjes realization/fiber
count remain explicitly unproved. See the updated GAPS.md.

## All-size endpoint-catenary theorem

The endpoint path subcase is now closed at the source-proof level, including
all real rates and every zero-rate boundary. Independent verification is
source-specific; consult the corresponding completed run receipt.

`HydrologyTree.catenary_standard_jacobian`
proves, for every n>=0 (n+1 stores), a fixed sign eps in {+1,-1}, independent of
all rates, such that the actual standard-coordinate Jacobian is

    eps * product_(i : Fin n) a_(i+1)^(n-i) f_i^(n-i-1).

The matrix is the actual `compartmentMatrix (pathTree n) x`; output coefficients
are the actual unreduced characteristic polynomial and root principal cofactor.
The Fréchet derivative, all-size physical induction and coordinate transport
are proved. `CoordinateEnergy` proves that the transport preserves the finite
coefficient dot product; the normalization is exactly a sign, not an arbitrary
nonzero scaling constant. The exact standard-coordinate singular locus is also
proved. The last outward rate and root leak need not be nonzero.

`PhysicalConstants` additionally proves, for every actual finite rooted tree
and every real rate vector, F(0)=product inward rates and P(0)=rootLeak*F(0).
Neither identity divides by a rate or assumes stability/positivity.

**These results do not close the all-branching-tree Jacobian, its exact factor
multiplicity theorem, or the complete positive-realization/fiber classification.**

## Global uniqueness at every regular path model

`catenary_global_fiber_at_regular_point` proves that a nonzero canonical
Jacobian at an endpoint-path model implies its ENTIRE real coefficient fiber
is a singleton. The competing rate vector is arbitrary: positivity, regularity
or proximity are not assumed for it. This is a constructive algebraic induction,
not just an inverse-function theorem. Root-leak recovery from P(0)/F(0), lower
numerator recovery, and the zero-dimensional terminal case are all proved.

This concerns complete unreduced characteristic/cofactor coefficient data.
It is not a blanket uniqueness assertion for a reduced response on zero-rate
boundaries; nor does it claim existence for an arbitrary prescribed Stieltjes
response. The branching-tree positive fiber classification remains unproved.
