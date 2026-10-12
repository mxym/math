import GaussianFractionalEquality
import Lean.Replay
import Lean

open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Adapted from the repository's continuum proof-closure replay.
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
    ``GaussianMeasureBridge.fractional_dual_equality_ae_winning]
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
