# Paper statements → actual Lean proof chain

Overall status: partial formalization. The all-tree rooted coefficient Jacobian
is proved; existence/counting, exact multiplicity and some variants remain.

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
| Uniform coordinate-boundary construction | `zero_outward_characteristic`, `zero_coordinate_coprime_witness` | All tree sizes; distinct inward rates, all outward rates zero |
| Exact individual-rate polynomial multiplicities | Not yet exported | Need complete divisibility/nondivisibility argument; the displayed factorization alone is insufficient |
| Exact signed resultant/Jacobian identity | Not yet exported | Zero-set equivalences do not replace the exact polynomial identity |
| All positive realizations and factorial count | Not yet exported | Interlacing, residue signs, every partition's realization, completeness and count remain |
| Nonroot leak / arbitrary external graph presentation | Not yet exported | Rooted OrderedTree main theorem does not silently include these transports |
| ODE all-input / controllability interpretations | Not yet exported | Algebraic resolvent and polynomial identities do not supply ODE semantics |

The audit roots include all owned declarations and their used dependencies.
Development compiler receipts are separate from independent source-bound
Lake/empty-kernel verification. No missing paper result is added as an axiom.
