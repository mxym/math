import HydrologyTree
import Lean.Replay
import Lean

open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Verification metaprogramming only; not an imported mathematical assumption.
partial def collect (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : Except String (Std.HashMap Name ConstantInfo) :=
  match todo with
  | [] => .ok seen
  | n :: rest =>
    if seen.contains n then collect env rest seen
    else match env.find? n with
    | none => .error s!"Missing dependency {n}"
    | some ci =>
      let extra := match ci with
        | .inductInfo v => v.all ++ v.ctors
        | .ctorInfo v => [v.induct]
        | .recInfo v => v.all
        | _ => []
      collect env (extra ++ ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n ci)

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := [
    ``HydrologyTree.Coeff,
    ``HydrologyTree.coeffNormedAddCommGroup,
    ``HydrologyTree.coeffNormedSpace,
    ``HydrologyTree.cut,
    ``HydrologyTree.degreeLTEquiv_coeff,
    ``HydrologyTree.cut_coeff,
    ``HydrologyTree.cut_coe,
    ``HydrologyTree.mulLM,
    ``HydrologyTree.mulCLM,
    ``HydrologyTree.mulCLM_apply,
    ``HydrologyTree.liftLM,
    ``HydrologyTree.liftCLM,
    ``HydrologyTree.coeff_eq_zero_of_bound,
    ``HydrologyTree.coe_lift,
    ``HydrologyTree.topMonomial,
    ``HydrologyTree.monicPoly,
    ``HydrologyTree.coe_monicPoly,
    ``HydrologyTree.bounded_natDegree,
    ``HydrologyTree.hasFDerivAt_monicPoly,
    ``HydrologyTree.monic_monicPoly,
    ``HydrologyTree.monicPoly_coeff_top,
    ``HydrologyTree.natDegree_monicPoly,
    ``HydrologyTree.cut_X_pow_of_le,
    ``HydrologyTree.joinLeadingLM,
    ``HydrologyTree.coe_joinLeadingLM,
    ``HydrologyTree.splitLeadingLM,
    ``HydrologyTree.splitLeadingLM_apply,
    ``HydrologyTree.split_joinLeading,
    ``HydrologyTree.join_splitLeading,
    ``HydrologyTree.leadingEquiv,
    ``HydrologyTree.leadingEquiv_apply,
    ``HydrologyTree.leadingEquiv_symm_apply,
    ``HydrologyTree.monicPoly_eq_leadingEquiv,
    ``HydrologyTree.leadingBasis,
    ``HydrologyTree.coe_cut_of_degree_lt,
    ``HydrologyTree.monic_reconstruct,
    ``HydrologyTree.repeatedBlock,
    ``HydrologyTree.repeatedBlock_apply,
    ``HydrologyTree.toMatrix_repeatedBlock,
    ``HydrologyTree.det_repeatedBlock,
    ``HydrologyTree.scaleChart,
    ``HydrologyTree.scaleChartDerivative,
    ``HydrologyTree.hasFDerivAt_scaleChart,
    ``HydrologyTree.toMatrix_scaleChartDerivative,
    ``HydrologyTree.det_scaleChartDerivative,
    ``HydrologyTree.scaleMonic,
    ``HydrologyTree.scaleMonic_eq_comp,
    ``HydrologyTree.scaleMonicDerivative,
    ``HydrologyTree.hasFDerivAt_scaleMonic,
    ``HydrologyTree.toMatrix_comp_equiv,
    ``HydrologyTree.monicScalingJacobian,
    ``HydrologyTree.monicScalingJacobian_eq,
    ``HydrologyTree.lowerBlock,
    ``HydrologyTree.lowerBlock_apply,
    ``HydrologyTree.toMatrix_lowerBlock,
    ``HydrologyTree.det_lowerBlock,
    ``HydrologyTree.PolyPair,
    ``HydrologyTree.GlueInput,
    ``HydrologyTree.pairBasis,
    ``HydrologyTree.coeff_natDegree_le,
    ``HydrologyTree.sylvCLM,
    ``HydrologyTree.sylvCLM_cut,
    ``HydrologyTree.monoSylv,
    ``HydrologyTree.lowSylv,
    ``HydrologyTree.glue,
    ``HydrologyTree.glueDerivative,
    ``HydrologyTree.hasFDerivAt_glue,
    ``HydrologyTree.gluingJacobian,
    ``HydrologyTree.gluingJacobian_eq_resultant_sq,
    ``HydrologyTree.rootChart,
    ``HydrologyTree.rootFiber,
    ``HydrologyTree.rootFiber_apply,
    ``HydrologyTree.rootChartDerivative,
    ``HydrologyTree.hasFDerivAt_rootChart,
    ``HydrologyTree.toMatrix_rootFiber,
    ``HydrologyTree.det_rootFiber,
    ``HydrologyTree.det_rootChartDerivative,
    ``HydrologyTree.shiftTop,
    ``HydrologyTree.shiftLow,
    ``HydrologyTree.rootPolynomial,
    ``HydrologyTree.rootPolynomial_cut,
    ``HydrologyTree.rootPolynomial_coeff_next,
    ``HydrologyTree.rootCoefficientMap,
    ``HydrologyTree.rootCoefficientMap_eq,
    ``HydrologyTree.hasFDerivAt_rootCoefficientMap,
    ``HydrologyTree.rootCoefficientJacobian,
    ``HydrologyTree.rootCoefficientJacobian_eq,
    ``HydrologyTree.degree_rootProduct,
    ``HydrologyTree.rootNumerator_degree_lt,
    ``HydrologyTree.rootPolynomial_monic,
    ``HydrologyTree.rootPolynomial_natDegree,
    ``HydrologyTree.rootPolynomial_reconstruct,
    ``HydrologyTree.OrderedTree,
    ``HydrologyTree.VertexValues,
    ``HydrologyTree.EdgeValues,
    ``HydrologyTree.TreeRates,
    ``HydrologyTree.parent_ne_child,
    ``HydrologyTree.parentIncidence,
    ``HydrologyTree.childWeighted,
    ``HydrologyTree.parentCLM,
    ``HydrologyTree.parentCLM_apply,
    ``HydrologyTree.rateChart,
    ``HydrologyTree.rateChartDerivative,
    ``HydrologyTree.hasFDerivAt_rateChart,
    ``HydrologyTree.toMatrix_rateChartDerivative,
    ``HydrologyTree.childWeighted_mul_parent,
    ``HydrologyTree.rateSchur_upperTriangular,
    ``HydrologyTree.rateSchur_diagonal,
    ``HydrologyTree.det_rateChartDerivative,
    ``HydrologyTree.physicalRateJacobian,
    ``HydrologyTree.physicalRateJacobian_eq,
    ``HydrologyTree.edgeMatrix,
    ``HydrologyTree.compartmentMatrix,
    ``HydrologyTree.sum_single_column,
    ``HydrologyTree.directed_transfer_column_sum,
    ``HydrologyTree.edgeMatrix_column_sum,
    ``HydrologyTree.compartment_column_sum,
    ``HydrologyTree.compartment_total_flux,
    ``HydrologyTree.compartment_diagonal_edge,
    ``HydrologyTree.compartment_diagonal,
    ``HydrologyTree.compartment_offdiag_nonneg,
    ``HydrologyTree.physicalCharacteristic,
    ``HydrologyTree.physicalRootCofactor,
    ``HydrologyTree.no_reversed_tree_edges,
    ``HydrologyTree.single_diagonal_offdiag,
    ``HydrologyTree.compartment_offdiag_formula,
    ``HydrologyTree.compartment_inward_entry,
    ``HydrologyTree.compartment_outward_entry,
    ``HydrologyTree.matrixRateCoordinates,
    ``HydrologyTree.matrixRateCoordinates_eq,
    ``HydrologyTree.hasFDerivAt_matrixRateCoordinates,
    ``HydrologyTree.matrixCoordinateJacobian,
    ``HydrologyTree.matrixCoordinateJacobian_eq,
    ``HydrologyTree.parentVertex,
    ``HydrologyTree.parentVertex_lt,
    ``HydrologyTree.parent_reaches_root,
    ``HydrologyTree.scalar_sub_principal,
    ``HydrologyTree.root_adjugate_eq_principal_det,
    ``HydrologyTree.root_inverse_entry_eq,
    ``HydrologyTree.root_resolvent_is_inverse,
    ``HydrologyTree.physicalRootResponse,
    ``HydrologyTree.physicalRootResponse_eq,
    ``HydrologyTree.physicalCoefficientMap,
    ``HydrologyTree.physicalCharacteristic_monic,
    ``HydrologyTree.physicalCharacteristic_natDegree,
    ``HydrologyTree.physicalRootCofactor_monic,
    ``HydrologyTree.physicalRootCofactor_natDegree,
    ``HydrologyTree.physicalCoefficientMap_first_reconstruct,
    ``HydrologyTree.physicalCoefficientMap_second_reconstruct]
  let cs ← match collect env roots {} with
    | .ok cs => pure cs
    | .error msg => throwError msg
  for (n, ci) in cs.toList do
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial dependency {n}"
    if ci.isAxiom then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom {n}"
  let base ← mkEmptyEnvironment 0
  let checked ← base.toKernelEnv.replay cs
  for root in roots do
    let some old := env.find? root | throwError "Original root missing {root}"
    let some new := checked.find? root | throwError "Replayed root missing {root}"
    unless old.type == new.type && old.levelParams == new.levelParams do
      throwError "Changed type or universes {root}"
  let names := (cs.toList.map (fun p => p.1.toString)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile "replayed-closure.txt" (String.intercalate "\n" names ++ "\n")
  let axioms := (cs.toList.filterMap (fun p => if p.2.isAxiom then some p.1.toString else none)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile "replayed-axioms.txt" (String.intercalate "\n" axioms ++ "\n")
  logInfo m!"EMPTY_KERNEL_REPLAY_PASS {cs.size} declarations; {roots.length} roots; trust level zero"
