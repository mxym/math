import ProofBundle
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
  let roots := [``OrbitalMarginals.tv_nonneg,
    ``OrbitalMarginals.tv_eq_zero_iff,
    ``OrbitalMarginals.tv_pos,
    ``OrbitalMarginals.tv_smul,
    ``OrbitalMarginals.tv_neg,
    ``OrbitalMarginals.kernel_of_match,
    ``OrbitalMarginals.tv_probability_difference_le_one,
    ``OrbitalMarginals.part_difference,
    ``OrbitalMarginals.part_sum,
    ``OrbitalMarginals.part_masses,
    ``OrbitalMarginals.jordan_probabilities,
    ``OrbitalMarginals.jordan_difference,
    ``OrbitalMarginals.jordan_match,
    ``OrbitalMarginals.jordan_disjoint,
    ``OrbitalMarginals.jordan_tv_one,
    ``OrbitalMarginals.signedBound_iff_pairBound,
    ``OrbitalMarginals.uniform_pos,
    ``OrbitalMarginals.uniform_probability,
    ``OrbitalMarginals.kernel_small_perturbation,
    ``OrbitalMarginals.uniformLawBound_iff_signedBound,
    ``OrbitalMarginals.uniformLawBound_iff_pairBound,
    ``OrbitalMarginals.isClosed_probability,
    ``OrbitalMarginals.probability_subset_cube,
    ``OrbitalMarginals.isCompact_probability,
    ``OrbitalMarginals.isClosed_feasiblePairs,
    ``OrbitalMarginals.isCompact_feasiblePairs,
    ``OrbitalMarginals.feasiblePairs_nonempty,
    ``OrbitalMarginals.exists_optimal_pair,
    ``OrbitalMarginals.exists_sharp_uniform_response,
    ``OrbitalMarginals.score_expectation,
    ``OrbitalMarginals.intervalDual_pairBound,
    ``OrbitalMarginals.mem_constraint_kernel,
    ``OrbitalMarginals.l1_norm,
    ``OrbitalMarginals.coordinate_norm_is_sharp,
    ``OrbitalMarginals.exists_exact_interval_dual,
    ``OrbitalMarginals.exact_real_primal_dual,
    ``OrbitalMarginals.score_range,
    ``OrbitalMarginals.oscillation_nonneg,
    ``OrbitalMarginals.oscillation_pairBound,
    ``OrbitalMarginals.exact_oscillation_duality,
    ``OrbitalMarginals.match_iff_imageMass,
    ``OrbitalMarginals.sum_translate,
    ``OrbitalMarginals.tv_translate,
    ``OrbitalMarginals.imageFeature_translate,
    ``OrbitalMarginals.kernel_translate,
    ``OrbitalMarginals.signedBound_all_atoms,
    ``OrbitalMarginals.uniformBound_all_atoms,
    ``OrbitalMarginals.group_action_exact_response,
    ``OrbitalMarginals.sum_conjugate,
    ``OrbitalMarginals.imageFeature_conjugate,
    ``OrbitalMarginals.kernel_conjugate,
    ``OrbitalMarginals.centralAverage_one,
    ``OrbitalMarginals.centralAverage_central,
    ``OrbitalMarginals.centralAverage_probability,
    ``OrbitalMarginals.centralAverage_kernel,
    ``OrbitalMarginals.centralAverage_sub,
    ``OrbitalMarginals.match_of_difference_kernel,
    ``OrbitalMarginals.centralAverage_match,
    ``OrbitalMarginals.group_action_central_primal,
    ``OrbitalMarginals.optimal_pair_tv_one,
    ``OrbitalMarginals.probability_parts_disjoint_of_tv_one,
    ``OrbitalMarginals.probability_perturbation_smaller,
    ``OrbitalMarginals.perturbation_match,
    ``OrbitalMarginals.positive_optimum_attained_locally,
    ``OrbitalMarginals.finite_rational_projection,
    ``OrbitalMarginals.rational_projection_mul,
    ``OrbitalMarginals.rationalize_pair_dual,
    ``OrbitalMarginals.exact_rational_primal_dual,
    ``OrbitalMarginals.fiberSize_pos,
    ``OrbitalMarginals.sum_pushLaw,
    ``OrbitalMarginals.pushLaw_liftLaw,
    ``OrbitalMarginals.sum_liftLaw,
    ``OrbitalMarginals.pushLaw_probability,
    ``OrbitalMarginals.liftLaw_probability,
    ``OrbitalMarginals.liftLaw_pushLaw,
    ``OrbitalMarginals.fiber_moment,
    ``OrbitalMarginals.lift_match,
    ``OrbitalMarginals.orbitalOf_smul,
    ``OrbitalMarginals.averagedCoefficient_smul,
    ``OrbitalMarginals.orbitalCoefficient_apply,
    ``OrbitalMarginals.orbital_score_expansion,
    ``OrbitalMarginals.averaged_score,
    ``OrbitalMarginals.orbital_dual_range,
    ``OrbitalMarginals.match_image_implies_orbital,
    ``OrbitalMarginals.exact_orbital_duality,
    ``OrbitalMarginals.orbital_moment_expansion,
    ``OrbitalMarginals.central_image_moment_smul,
    ``OrbitalMarginals.central_image_moment_orbital,
    ``OrbitalMarginals.central_match_iff_orbital,
    ``OrbitalMarginals.orbitalFeatures_conjugate,
    ``OrbitalMarginals.sharpConstant_eq_optimum,
    ``OrbitalMarginals.sharpConstant_trivial_kernel,
    ``OrbitalMarginals.cast_orbitalFeaturesQ,
    ``OrbitalMarginals.classFeaturesQ_mk,
    ``OrbitalMarginals.real_classFeatures_mk,
    ``OrbitalMarginals.class_mk_conjugate,
    ``OrbitalMarginals.class_identity_iff,
    ``OrbitalMarginals.class_fiber_identity,
    ``OrbitalMarginals.class_lift_identity,
    ``OrbitalMarginals.class_push_identity,
    ``OrbitalMarginals.class_lift_central,
    ``OrbitalMarginals.central_class_constant,
    ``OrbitalMarginals.class_lift_push,
    ``OrbitalMarginals.class_matrix_is_average,
    ``OrbitalMarginals.class_lift_match,
    ``OrbitalMarginals.central_class_match,
    ``OrbitalMarginals.orbital_score_class,
    ``OrbitalMarginals.class_oscillation,
    ``OrbitalMarginals.universal_orbital_theorem,
    ``OrbitalMarginals.kernelRatios_all_atoms,
    ``OrbitalMarginals.sharpConstant_all_atoms,
    ``OrbitalMarginals.normalized_kernel_attainment,
    ``OrbitalMarginals.sharp_attainment_all_atoms,
    ``OrbitalMarginals.orbital_span_exact_minimum,
    ``OrbitalMarginals.empty_features_nonvacuous,
    ``OrbitalMarginals.one_atom_zero_endpoint,
    ``OrbitalMarginals.jordan_requires_zero_mass]
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
  logInfo m!"EMPTY_KERNEL_REPLAY_PASS {cs.size} declarations; {roots.length} roots; trust level zero"
