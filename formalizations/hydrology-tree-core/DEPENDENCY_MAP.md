# Paper statements → actual Lean proof chain

Overall status: partial formalization. The all-tree rooted coefficient Jacobian
and exact polynomial rate multiplicities are proved; positive existence/counting
and the graph/leak/ODE variants remain.

| Statement | Main Lean entries | Exact scope |
|---|---|---|
| Physical rate matrix and conservative balance | `compartmentMatrix`, `compartment_column_sum`, `compartment_total_flux` | Actual entries, arbitrary real rates |
| Genuine principal child models | `physicalBranch_eq_childTree`, `physicalBranch_charpoly_eq`, `physicalBranch_cofactor_eq` | Original exit-to-parent diagonal retained |
| Independent original rate coordinates | `originalWorkEquiv_apply`, `originalWorkEquiv_dot` | Rate-independent bijection and exact coefficient-dot preservation |
| Actual child coefficient preparation | `prepareFamilyEquiv`, `prepareFamilyEquiv_dot`, `actualBranchInputs_coefficients` | Actual polynomials; no assumed child-Jacobian semantic bridge |
| All-child polynomial scaling/gluing/root step | `familyGlueJacobian_eq_pairwise`, `normalizedBranchStep_jacobian` | All degrees/rates, including zero scales and repeated roots |
| Full physical pipeline | `treePipeline_actual`, `treeCanonicalJacobian_recurrence` | End-to-end physical identification and discharged smaller-child induction |
| Main all-tree standard Jacobian | `full_tree_standard_jacobian` | Actual Frechet derivative, fixed sign for all rates; products on original vertices/edges |
| Jacobian regularity and sibling coprimality | `treeJacobian_ne_zero_iff_coprime` | Nonzero real internal rates; root leak unrestricted |
| Positive spectral singular set | `positive_tree_jacobian_zero_iff_collision` | Positive internal rates; actual real sibling principal spectra |
| Full positive Stieltjes modes | `positive_tree_jacobian_iff_full_modes` | Positive root leak and internal rates; energy/spectral proof imported, not assumed |
| Global uniqueness per fixed subtree assignment | `regular_tree_assignment_unique` | Arbitrary real competitor; not uniqueness from root response alone |
| Formal symbolic/analytic derivative identification | `formalTreeJacobian_evaluate`, `formal_catenary_jacobian_polynomial` | Actual symbolic characteristic/cofactor coefficients and formal partial derivatives, matched to actual Frechet derivatives at every real rate vector |
| Uniform coordinate-boundary construction | `zero_outward_characteristic`, `zero_coordinate_coprime_witness` | All tree sizes; distinct inward rates, all outward rates zero |
| Exact individual-rate polynomial multiplicities | `formalTreeJacobian_exact_powers`, `formalTreeJacobian_inward_multiplicity`, `formalTreeJacobian_outward_multiplicity` | Polynomial prime multiplicity of the formally differentiated actual coefficient determinant; nondivisibility by the next power proved, including zero exponents |
| Exact signed resultant/Jacobian identity | `full_tree_resultant_jacobian`, `physicalResultant_jacobian_square` | Fixed tree-dependent sign, all real rates and all degenerate boundaries |
| All positive realizations and factorial count | Not yet exported | Interlacing, residue signs, every partition's realization, completeness and count remain |
| Nonroot leak / arbitrary external graph presentation | Not yet exported | Rooted OrderedTree main theorem does not silently include these transports |
| ODE all-input / controllability interpretations | Not yet exported | Algebraic resolvent and polynomial identities do not supply ODE semantics |

The audit roots include all owned declarations and their used dependencies.
Development compiler receipts are separate from independent source-bound
Lake/empty-kernel verification. No missing paper result is added as an axiom.


### Positive fiber completion

The prior existence/at-most-one-assignment obligations are now complemented by
`PositiveFiberAllocation` (unique exhaustive factor extraction),
`PositiveFiberRecovery` (actual child numerator recovery),
`PositiveFiberEquivalence` (surjective and injective actual root assembly),
`RecursiveFiberClassification` (complete recursive allocation bijection),
`TreeFiberCombinatorics` (original-subtree factorial identity),
`PositiveFiberCount` (actual finiteness and exact cardinality), and
`PositiveResponseFiber` (response-only equivalence, exact count and regularity).
These replace, rather than assume, the previously missing positive-fiber count.


### Unrestricted real-fiber strengthening

`RealFactorAllocation` proves real splitting and labelled allocation of every
actual child factor without any sign condition on the competing rate vector.
`RealFiberRigidity` recovers the normalized child data from a positive reference
and proves automatic strict positivity by strong induction.
`RealFiberClassification` transports the full recursive bijection and exact
cardinality to ALL real models sharing the actual target root response. No
additional sign-constrained domain is hidden in these unrestricted fibers.


`DischargeFiber` proves the actual leak-scaled root transfer, identifies the
leak from transfer equality, and gives exact all-real discharge-fiber cardinality.
The real-fiber note under research/hydrology-tree-real-fibers explains the complete
mathematical proof; it is not a replacement for the checked Lean dependencies.


### Actual ODE forward bridge

LinearForcedODE -> ScalarForcedODE; RootModalData plus the actual spectral
construction -> PhysicalModalConstruction; scalar integral solutions and the
proved coordinate witness -> ModalForcedODE. StieltjesWeightedMatching proves
that the complete coefficient pair fixes every weighted spectral sum.
PhysicalForcedODE and FullResponseDynamics discharge the modal and positivity
inputs for original physical matrices. PhysicalMassODE proves the actual storage
balance. The reverse time-domain identification and state-space reachability
obligations remain explicit in GAPS.md.
