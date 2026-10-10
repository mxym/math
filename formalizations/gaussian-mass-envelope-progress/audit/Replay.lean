import GaussianSets
import GaussianEntropy
import Lean.Replay
import Lean

open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Verifier metaprogram adapted from the existing Gaussian replay in this repository.
-- The use of partial recursion here is not a mathematical proof dependency.
partial def collectProofClosure (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : Except String (Std.HashMap Name ConstantInfo) :=
  match todo with
  | [] => .ok seen
  | n :: rest =>
    if seen.contains n then collectProofClosure env rest seen
    else match env.find? n with
    | none => .error s!"Missing dependency {n}"
    | some ci =>
      let extra := match ci with
        | .inductInfo v => v.all ++ v.ctors
        | .ctorInfo v => [v.induct]
        | .recInfo v => v.all
        | _ => []
      collectProofClosure env (extra ++ ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n ci)

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := [
    ``GaussianMeasureBridge.integrable_standardDensity,
    ``GaussianMeasureBridge.continuous_standardDensity,
    ``GaussianMeasureBridge.gaussianTail_nonneg,
    ``GaussianMeasureBridge.gaussianTail_pos,
    ``GaussianMeasureBridge.gaussianTail_eq_probability,
    ``GaussianMeasureBridge.gaussianTail_lt_one,
    ``GaussianMeasureBridge.gaussianTail_sub_eq_interval,
    ``GaussianMeasureBridge.gaussianTail_hasDerivAt,
    ``GaussianMeasureBridge.gaussianTail_tendsto_zero,
    ``GaussianMeasureBridge.integrable_sq_mul_standardDensity,
    ``GaussianMeasureBridge.mul_standardDensity_hasDerivAt,
    ``GaussianMeasureBridge.mul_standardDensity_tendsto_zero,
    ``GaussianMeasureBridge.gaussianTail_secondMoment,
    ``GaussianMeasureBridge.gaussianTail_threshold_le_firstMoment,
    ``GaussianMeasureBridge.gaussianTail_centered_secondMoment_nonneg,
    ``GaussianMeasureBridge.thresholdHazard_pos,
    ``GaussianMeasureBridge.thresholdHazard_mul_tail,
    ``GaussianMeasureBridge.threshold_le_hazard,
    ``GaussianMeasureBridge.thresholdHazard_variance_bound,
    ``GaussianMeasureBridge.thresholdHazard_hasDerivAt,
    ``GaussianMeasureBridge.thresholdHazard_monotone,
    ``GaussianMeasureBridge.squaredHazard_logTail_hasDerivAt,
    ``GaussianMeasureBridge.squaredHazard_logTail_antitone,
    ``GaussianMeasureBridge.squared_hazard_log_lipschitz_threshold,
    ``GaussianMeasureBridge.gaussianTail_continuous,
    ``GaussianMeasureBridge.gaussianTail_strictAnti,
    ``GaussianMeasureBridge.gaussianTail_tendsto_one,
    ``GaussianMeasureBridge.exists_unique_gaussianTail_eq,
    ``GaussianMeasureBridge.gaussianTail_upperQuantile,
    ``GaussianMeasureBridge.upperQuantile_antitone,
    ``GaussianMeasureBridge.massHazard_eq_thresholdHazard,
    ``GaussianMeasureBridge.squared_hazard_log_lipschitz,
    ``GaussianMeasureBridge.gaussian_unit_halfspace_mass,
    ``GaussianMeasureBridge.FractionalPartition.one_cell_threshold_bound,
    ``GaussianMeasureBridge.FractionalPartition.one_cell_norm_bound,
    ``GaussianMeasureBridge.FractionalPartition.one_cell_profile_bound,
    ``GaussianMeasureBridge.FractionalPartition.sum_moment_sq_le_profile,
    ``GaussianMeasureBridge.twoCellPartition_mass,
    ``GaussianMeasureBridge.twoCellPartition_moment,
    ``GaussianMeasureBridge.measurable_set_moment_bound,
    ``GaussianMeasureBridge.measurable_sets_moment_sq_le_profile,
    ``GaussianMeasureBridge.prescribed_mass_measurable_sets_bound,
    ``GaussianMeasureBridge.gaussianTail_exp_moment_bound,
    ``GaussianMeasureBridge.gaussianTail_hazard_entropy_bound,
    ``GaussianMeasureBridge.gaussian_profile_entropy_bound,
    ``GaussianMeasureBridge.gaussianReal_halfline_firstMoment,
    ``GaussianMeasureBridge.gaussian_unit_halfspace_flux]
  let cs ← match collectProofClosure env roots {} with
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
