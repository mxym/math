import GaussianFourProgress
import Lean.Replay
import Lean

open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Meta-only checker adapted from the existing actual-measure replay.
-- Its partial collector is not in the verified mathematical dependency closure.
-- Missing constants fail closed. Inductive companions are included.
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
    ``GaussianMeasureBridge.FractionalPartition.norm_label_le_one,
    ``GaussianMeasureBridge.FractionalPartition.integrable_label,
    ``GaussianMeasureBridge.FractionalPartition.integrable_weighted_id,
    ``GaussianMeasureBridge.FractionalPartition.mass_nonneg,
    ``GaussianMeasureBridge.FractionalPartition.sum_mass,
    ``GaussianMeasureBridge.FractionalPartition.sum_moment,
    ``GaussianMeasureBridge.FractionalPartition.inner_moment,
    ``GaussianMeasureBridge.le_scoreMax,
    ``GaussianMeasureBridge.integrable_score,
    ``GaussianMeasureBridge.integrable_scoreMax,
    ``GaussianMeasureBridge.continuous_scoreMax,
    ``GaussianMeasureBridge.FractionalPartition.integrable_weighted_score,
    ``GaussianMeasureBridge.FractionalPartition.integral_weighted_score,
    ``GaussianMeasureBridge.FractionalPartition.price_dual,
    ``GaussianMeasureBridge.integral_score,
    ``GaussianMeasureBridge.scoreMax_le_add_norm,
    ``GaussianMeasureBridge.scoreMax_abs_sub_le,
    ``GaussianMeasureBridge.expectedScore_lipschitz,
    ``GaussianMeasureBridge.continuous_priceObjective,
    ``GaussianMeasureBridge.scoreMax_sub_const,
    ``GaussianMeasureBridge.priceObjective_sub_const,
    ``GaussianMeasureBridge.expectedScore_nonneg_of_zero,
    ``GaussianMeasureBridge.weighted_price_le_objective,
    ``GaussianMeasureBridge.exists_price_minimizer,
    ``GaussianMeasureBridge.gaussian_hyperplane_null,
    ``GaussianMeasureBridge.ae_scores_pairwise_ne,
    ``GaussianMeasureBridge.measurableSet_winningCell,
    ``GaussianMeasureBridge.ae_unique_winner,
    ``GaussianMeasureBridge.gaussian_open_pos,
    ``GaussianMeasureBridge.coordinateShift_zero,
    ``GaussianMeasureBridge.coordinateShift_dist_le,
    ``GaussianMeasureBridge.coordinateScore_lipschitz,
    ``GaussianMeasureBridge.scoreMax_eq_winning_score,
    ``GaussianMeasureBridge.winningCell_disjoint,
    ``GaussianMeasureBridge.coordinateScore_hasDerivAt,
    ``GaussianMeasureBridge.expectedScore_coordinate_derivative,
    ``GaussianMeasureBridge.weighted_price_coordinate,
    ``GaussianMeasureBridge.priceObjective_coordinate_derivative,
    ``GaussianMeasureBridge.exists_balancing_prices,
    ``GaussianMeasureBridge.winningPartition_mass,
    ``GaussianMeasureBridge.winningPartition_dual_attainment,
    ``GaussianMeasureBridge.balanced_price_is_minimizer,
    ``GaussianMeasureBridge.scoreMid_le,
    ``GaussianMeasureBridge.weighted_priceMid,
    ``GaussianMeasureBridge.minimizers_jensen_gap_zero,
    ``GaussianMeasureBridge.common_maximizer_of_jensen_zero,
    ``GaussianMeasureBridge.minimizers_score_difference_constant,
    ``GaussianMeasureBridge.balancing_prices_unique_mod_const,
    ``GaussianMeasureBridge.actual_gaussian_primal_dual,
    ``GaussianMeasureBridge.fractional_dual_equality_ae_winning,
    ``GaussianFourGlobal.densityCap_pos,
    ``GaussianFourGlobal.densityCap_eq,
    ``GaussianFourGlobal.gaussianPDF_le_densityCap,
    ``GaussianFourGlobal.tent_nonneg,
    ``GaussianFourGlobal.tent_le,
    ``GaussianFourGlobal.continuous_tent,
    ``GaussianFourGlobal.tent_eq_zero_outside,
    ``GaussianFourGlobal.integrable_tent,
    ``GaussianFourGlobal.integral_tent,
    ``GaussianFourGlobal.gaussianReal_tent_bound,
    ``GaussianFourGlobal.unit_inner_law,
    ``GaussianFourGlobal.gaussian_inner_tent_bound,
    ``GaussianFourGlobal.integrable_inner_tent,
    ``GaussianFourGlobal.two_label_tent,
    ``GaussianFourGlobal.pair_label_sum_le_one,
    ``GaussianFourGlobal.fractional_pair_separation,
    ``GaussianFourGlobal.fractional_equal_mass_pair_separation,
    ``GaussianFourGlobal.separationConstant_pos,
    ``GaussianFourGlobal.separationConstant_eq,
    ``GaussianFourGlobal.balanced_winning_moment_separation,
    ``GaussianFourGlobal.balanced_winning_moment_norm_separation,
    ``GaussianFourGlobal.eventually_winningCell,
    ``GaussianFourGlobal.eventually_winning_memberships,
    ``GaussianFourGlobal.ae_tendsto_winning_indicator,
    ``GaussianFourGlobal.tendsto_winning_setIntegral,
    ``GaussianFourGlobal.tendsto_winning_mass,
    ``GaussianFourGlobal.winningPartition_moment_eq_setIntegral,
    ``GaussianFourGlobal.tendsto_winning_moment,
    ``GaussianFourGlobal.balanced_winning_limit,
    ``GaussianFourGlobal.tendsto_moment_of_residual,
    ``GaussianFourGlobal.residual_limit_pair_separation,
    ``GaussianFourGlobal.residual_limit_injective,
    ``GaussianFourGlobal.residual_limit_multiplier_pos,
    ``GaussianFourGlobal.balanced_residual_limit,
    ``GaussianFourGlobal.winningCell_pos_scale,
    ``GaussianFourGlobal.balanced_limit_self_moment,
    ``GaussianFourGlobal.uniformPartition_mass,
    ``GaussianFourGlobal.uniformPartition_moment,
    ``GaussianFourGlobal.balancedValue_eq_minimizer,
    ``GaussianFourGlobal.balancedValue_attained,
    ``GaussianFourGlobal.balancedValue_le_price,
    ``GaussianFourGlobal.fractional_value_le_balancedValue,
    ``GaussianFourGlobal.balancedValue_nonneg,
    ``GaussianFourGlobal.gaussianRadius_nonneg,
    ``GaussianFourGlobal.scoreMax_score_le,
    ``GaussianFourGlobal.expectedScore_score_le,
    ``GaussianFourGlobal.balancedValue_score_le,
    ``GaussianFourGlobal.balancedValue_abs_sub_le,
    ``GaussianFourGlobal.balancedValue_lipschitz,
    ``GaussianFourGlobal.continuous_balancedValue,
    ``GaussianFourGlobal.expectedScore_zero_zero,
    ``GaussianFourGlobal.balanced_price_bound,
    ``GaussianFourGlobal.scoreMax_scale_nonneg,
    ``GaussianFourGlobal.priceObjective_scale_nonneg,
    ``GaussianFourGlobal.balancedValue_zero,
    ``GaussianFourGlobal.balancedValue_pos_scale,
    ``GaussianFourGlobal.balancedValue_scale_nonneg,
    ``GaussianFourGlobal.momentEnergy_nonneg,
    ``GaussianFourGlobal.uniformPartition_energy,
    ``GaussianFourGlobal.self_partitionValue,
    ``GaussianFourGlobal.energy_le_balancedValue,
    ``GaussianFourGlobal.sum_normalizedMoments,
    ``GaussianFourGlobal.normalizedMoments_energy_one,
    ``GaussianFourGlobal.normalized_partitionValue,
    ``GaussianFourGlobal.sqrt_energy_le_normalized_value,
    ``GaussianFourGlobal.winning_labels_of_energy_value_equality,
    ``GaussianFourGlobal.SetPartition.toFractional_mass,
    ``GaussianFourGlobal.SetPartition.toFractional_moment,
    ``GaussianFourGlobal.SetPartition.sum_set_moment,
    ``GaussianFourGlobal.SetPartition.moment_eq_of_ae_cells,
    ``GaussianFourGlobal.SetPartition.mass_quarter,
    ``GaussianFourGlobal.SetPartition.energy_le_value,
    ``GaussianFourGlobal.SetPartition.normalized_reduction,
    ``GaussianFourGlobal.scoreMap_apply,
    ``GaussianFourGlobal.scoreMap_inner,
    ``GaussianFourGlobal.gaussian_inner_law,
    ``GaussianFourGlobal.norm_sum_smul_sq_of_gram_eq,
    ``GaussianFourGlobal.scoreLaw_eq_of_gram_eq,
    ``GaussianFourGlobal.continuous_coordinateMax,
    ``GaussianFourGlobal.expectedScore_eq_scoreLaw_integral,
    ``GaussianFourGlobal.expectedScore_eq_of_gram_eq,
    ``GaussianFourGlobal.priceObjective_eq_of_gram_eq,
    ``GaussianFourGlobal.balancedValue_eq_of_gram_eq,
    ``GaussianFourGlobal.balancedValue_isometric_embedding,
    ``GaussianFourGlobal.uniform_not_ae_indicator]
  let cs ← match collect env roots {} with
    | .ok cs => pure cs
    | .error msg => throwError msg
  for (n, ci) in cs.toList do
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial dependency {n}"
    if ci.isAxiom then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom {n}"
  let base ← mkEmptyEnvironment 0
  let verified ← base.toKernelEnv.replay cs
  for root in roots do
    let some original := env.find? root | throwError "Original root missing {root}"
    let some checked := verified.find? root | throwError "Replayed root missing {root}"
    unless original.type == checked.type && original.levelParams == checked.levelParams do
      throwError "Changed type/levels {root}"
  let names := (cs.toList.map (fun p => p.1.toString)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile "replayed-closure.txt" (String.intercalate "\n" names ++ "\n")
  let axioms := (cs.toList.filterMap (fun p => if p.2.isAxiom then some p.1.toString else none)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile "replayed-axioms.txt" (String.intercalate "\n" axioms ++ "\n")
  logInfo m!"EMPTY_KERNEL_REPLAY_PASS {cs.size} declarations; {roots.length} roots; trust level zero"
