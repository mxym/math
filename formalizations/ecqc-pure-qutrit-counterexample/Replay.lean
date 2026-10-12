import ECQC
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
    ``ECQC.IsDensity,
    ``ECQC.pureState,
    ``ECQC.pureState_posSemidef,
    ``ECQC.vonNeumannEntropy,
    ``ECQC.eigenvalue_zero_or_scale,
    ``ECQC.entropy_scaled_projection,
    ``ECQC.partialTraceRight,
    ``ECQC.partialTraceLeft,
    ``ECQC.born,
    ``ECQC.born_pureState,
    ``ECQC.localOutcome,
    ``ECQC.bornTable,
    ``ECQC.matrixEntropy,
    ``ECQC.matrixEntropy_eq,
    ``ECQC.quantumMutualInformation,
    ``ECQC.shannon,
    ``ECQC.mutualInformation,
    ``ECQC.IsCompleteMUB,
    ``ECQC.retainedValues,
    ``ECQC.ecqcScore,
    ``ECQC.Qutrit.Q,
    ``ECQC.Qutrit.QQ,
    ``ECQC.Qutrit.coefficients,
    ``ECQC.Qutrit.psi,
    ``ECQC.Qutrit.rho,
    ``ECQC.Qutrit.reduced,
    ``ECQC.Qutrit.psi_normalized,
    ``ECQC.Qutrit.rho_posSemidef,
    ``ECQC.Qutrit.rho_trace,
    ``ECQC.Qutrit.rho_density,
    ``ECQC.Qutrit.rho_hermitian,
    ``ECQC.Qutrit.rho_idempotent,
    ``ECQC.Qutrit.partialTraceRight_rho,
    ``ECQC.Qutrit.partialTraceLeft_rho,
    ``ECQC.Qutrit.reduced_hermitian,
    ``ECQC.Qutrit.reduced_trace,
    ``ECQC.Qutrit.reduced_scaled_projection,
    ``ECQC.Qutrit.omega,
    ``ECQC.Qutrit.alpha,
    ``ECQC.Qutrit.beta,
    ``ECQC.Qutrit.basis,
    ``ECQC.Qutrit.sqrt3_sq,
    ``ECQC.Qutrit.sqrt3_pow3,
    ``ECQC.Qutrit.sqrt3_pow4,
    ``ECQC.Qutrit.alpha_mul_omega,
    ``ECQC.Qutrit.basis_orthonormal,
    ``ECQC.Qutrit.basis_mutually_unbiased,
    ``ECQC.Qutrit.probabilityTable,
    ``ECQC.Qutrit.bornTable_eq,
    ``ECQC.Qutrit.probabilityTable_nonneg,
    ``ECQC.Qutrit.probabilityTable_total,
    ``ECQC.Qutrit.actual_born_probabilities,
    ``ECQC.Qutrit.log_half,
    ``ECQC.Qutrit.log_quarter,
    ``ECQC.Qutrit.reduced_density,
    ``ECQC.Qutrit.rho_spectral_entropy,
    ``ECQC.Qutrit.reduced_spectral_entropy,
    ``ECQC.Qutrit.rho_quantum_mutual_information,
    ``ECQC.Qutrit.probabilityTable_row_entropy,
    ``ECQC.Qutrit.probabilityTable_column_entropy,
    ``ECQC.Qutrit.probabilityTable_joint_entropy,
    ``ECQC.Qutrit.probabilityTable_mutual_information,
    ``ECQC.Qutrit.measured_mutual_information,
    ``ECQC.Qutrit.completeMUB,
    ``ECQC.Qutrit.retained_sum,
    ``ECQC.Qutrit.retainedValues_singleton,
    ``ECQC.Qutrit.ecqc_score_eq,
    ``ECQC.Qutrit.ecqc_minimum_attained,
    ``ECQC.Qutrit.exact_excess,
    ``ECQC.Qutrit.strict_violation,
    ``ECQC.Qutrit.pure_qutrit_counterexample,
    ``ECQC.Qutrit.exists_pure_qutrit_counterexample,
    ``ECQC.Qutrit.pure_prime_dimensional_ecqc_is_false]
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
  IO.FS.writeFile "replayed-roots.txt" (String.intercalate "\n" (roots.map Name.toString) ++ "\n")
  let names := (cs.toList.map (fun p => p.1.toString)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile "replayed-closure.txt" (String.intercalate "\n" names ++ "\n")
  let axioms := (cs.toList.filterMap (fun p => if p.2.isAxiom then some p.1.toString else none)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile "replayed-axioms.txt" (String.intercalate "\n" axioms ++ "\n")
  logInfo m!"EMPTY_KERNEL_REPLAY_PASS {cs.size} declarations; {roots.length} roots; trust level zero"
