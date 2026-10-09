import APPT.Quantum.SpectralNecessity
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
  let roots := [``APPT.Quantum.diagonal_appt_necessary_matrices,
    ``APPT.Quantum.selected_corner_posSemidef,
    ``APPT.Quantum.sortedSpectrum_antitone,
    ``APPT.Quantum.sortedSpectrum_nonneg,
    ``APPT.Quantum.actual_diagonalization,
    ``APPT.Quantum.appt_eigenvalue_diagonal,
    ``APPT.Quantum.density_eigenvalue_diagonal,
    ``APPT.Quantum.NecessarySpectrum.sum_one,
    ``APPT.Quantum.NecessarySpectrum.purity_eq_sum_sq,
    ``APPT.Quantum.NecessarySpectrum.matrices_posSemidef,
    ``APPT.Quantum.density_appt_has_sorted_spectrum]
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
  IO.FS.writeFile "necessity-replayed-roots.txt" (String.intercalate "\n" (roots.map Name.toString) ++ "\n")
  let names := (cs.toList.map (fun p => p.1.toString)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile "necessity-replayed-closure.txt" (String.intercalate "\n" names ++ "\n")
  let axioms := (cs.toList.filterMap (fun p => if p.2.isAxiom then some p.1.toString else none)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile "necessity-replayed-axioms.txt" (String.intercalate "\n" axioms ++ "\n")
  logInfo m!"NECESSITY_EMPTY_KERNEL_REPLAY_PASS {cs.size} declarations; {roots.length} roots; trust level zero"
