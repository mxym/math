# Written theorems to checked Lean: current correspondence

Status: partial formalization, not a proof of the all-tree theorem or all its
corollaries. The target is the actual monic characteristic/cofactor coefficient
map for a conservative bidirected tree with one external leak.

| Required statement | Current Lean theorem | Remaining connection |
|---|---|---|
| Coefficient charts and reconstruction of actual monic polynomials | `Coefficients`, `LeadingCoefficients`, `monic_reconstruct` | No sampled coefficient model is substituted. |
| Two-child polynomial gluing | `hasFDerivAt_glue`, `gluingJacobian_eq_resultant_sq` | All degrees, all numerator coefficients, common roots and degree-zero cases included. Full arbitrary-family induction is now `familyGlueJacobian_eq_pairwise`, with actual numerator equality and proved second-order regularity. |
| Numerator scaling R=c F | `hasFDerivAt_scaleMonic`, `monicScalingJacobian_eq` | Actual monic polynomial coefficients; determinant c^n at every scalar, including zero. |
| Root update P=(X+d)F-N | `hasFDerivAt_rootCoefficientMap`, `rootCoefficientJacobian_eq`, `rootPolynomial_monic`, `rootPolynomial_natDegree` | Actual polynomial operation and its Frechet derivative; no assumed Jacobian. Identification with a tree characteristic determinant remains. |
| Rate chart (lambda,a,f) -> (d,c) | `matrixCoordinateJacobian_eq`, `hasFDerivAt_matrixRateCoordinates` | Complete for every topologically numbered rooted tree, all real rates including zero; arbitrary graph reindexing and observation-root/leak-root change still need integration. |
| Actual characteristic/cofactor objects | `physicalCoefficientMap`, both reconstruction theorems, `physicalRootResponse_eq` | Actual matrix, conservation, rates, charpoly and cofactor semantics are proved. Single-edge determinant/cofactor recursion and arbitrary-branch matrix assembly are now proved in `RootAttachment` and `BranchAssembly`. PhysicalLeaf now proves an all-size last-leaf recurrence directly for the original OrderedTree matrix. RootBranches, BranchMatrixSupport and physical_root_block_decomposition now prove the exact original matrix root/branch transport. ChildMatrix now proves complete identification with a smaller physical OrderedTree, retaining the exit leak. Global rate-coordinate permutation and derivative induction remain. |
| All-tree Jacobian factorization | Not yet exported | Arbitrary child-family Jacobian is now proved. The remaining chain rule and global tree induction must connect actual subtree matrix coefficients; basis signs/reindexing must be checked. |
| Exact edge multiplicities, catenary and tree conjecture statements | Not yet exported | Requires full actual-tree factorization; exact multiplicities additionally need no hidden rate factors in resultants. |
| Cancellation resultant identity | Not yet exported | All-tree induction, multiplicativity and degree bookkeeping. At zero rates, do not conflate reduced response with unreduced coefficient data. |
| Strictly positive singular-locus equivalences | Not yet exported | Actual diagonal symmetrization, stability, principal block spectra and no unproved minimality assertion. |
| Complete positive realization and fiber count | Not yet exported | Stieltjes interlacing/residue signs, complete constructive inverse, uniqueness for each assignment, positivity/conservation, factorial count. |
| Topology ambiguity, global components, physical discharge interpretation | Not yet exported | All claimed consequences need their actual supporting definitions and theorem statements. |

The isolated compiler session is development infrastructure. Its status is not a
proof certificate. Only the separate source-bound Lake/replay/negative-control
workflow can certify a completed source checkpoint. No main theorem is exported
with its conclusion or a missing geometric/algebraic bridge as a hypothesis.

## Updated end-to-end coverage

- Child renumbering and all matrix/characteristic/cofactor transport:
  `physicalBranch_eq_childTree`, `physicalBranch_charpoly_eq`,
  `physicalBranch_cofactor_eq`, `childEdgeCount_lt`.
- Full independent rate input chart: `ratePartitionEquiv`,
  `ratePartition_child`, `ratePartition_unique_original` (see actual ROOTS.txt
  for the exported uniqueness declaration's precise name).
- Nonlinear root coupling: `rootCoupling_jacobian`,
  `rootCoupling_physical_coordinates`, `actualCoupling_jacobian`.
- Actual original-tree recursions: `physicalRootCofactor_child_product`,
  `physicalCharacteristic_child_recursion`.
- Full common-root classification under nonzero internal edges, all tree sizes
  and arbitrary real field extensions: `physicalCommonRoot_iff_siblingCollision`.
  This has no assumed block determinant, child matrix transport or cancellation
  statement. Its proof uses the proved local algebra and well-founded child
  recursion. It does not assert the unfinished global Jacobian equivalence.

The global coefficient-Jacobian chain and its basis/orientation assembly,
exact multiplicities, positive spectral consequences and complete positive
inverse/fiber classification remain the explicit missing mathematical work.

### Endpoint-path completion

The actual coefficient map, its Fréchet derivative and all-size determinant
recurrence are `PathPhysical`, `PathInduction`, `CatenaryJacobian`.
`CatenaryCanonical`, `CoordinateEnergy` and `CatenaryOrientation` prove transport
to standard ascending P/F coefficient and physical-array coordinates with a
fixed factor of magnitude exactly one. `catenary_standard_singular_locus` includes
all zero boundaries. This is an unconditional endpoint-path theorem, not the
all-tree induction. `PhysicalConstants` proves P(0)=lambda F(0) and F(0)=prod a
for every tree with arbitrary real rates, including zero.
