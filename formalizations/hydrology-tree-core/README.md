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
