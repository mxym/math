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
| Actual characteristic/cofactor objects | `physicalCoefficientMap`, both reconstruction theorems, `physicalRootResponse_eq` | Actual matrix, conservation, rates, charpoly and cofactor semantics are proved. Single-edge determinant/cofactor recursion and arbitrary-branch matrix assembly are now proved in `RootAttachment` and `BranchAssembly`. PhysicalLeaf now proves an all-size last-leaf recurrence directly for the original OrderedTree matrix. Full root-child decomposition transport and global derivative induction remain. |
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
