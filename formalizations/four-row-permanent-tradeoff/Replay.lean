import FourRowTradeoff
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
    ``FourRowTradeoff.Row,
    ``FourRowTradeoff.Mat,
    ``FourRowTradeoff.rowSq,
    ``FourRowTradeoff.symPair,
    ``FourRowTradeoff.altPair,
    ``FourRowTradeoff.symEnergy,
    ``FourRowTradeoff.altEnergy,
    ``FourRowTradeoff.overlap,
    ``FourRowTradeoff.collision,
    ``FourRowTradeoff.sharpConstant,
    ``FourRowTradeoff.normSq_as_sq,
    ``FourRowTradeoff.norm_sum_mul_sq_le,
    ``FourRowTradeoff.rowSq_nonneg,
    ``FourRowTradeoff.symEnergy_nonneg,
    ``FourRowTradeoff.altEnergy_nonneg,
    ``FourRowTradeoff.overlap_nonneg,
    ``FourRowTradeoff.collision_nonneg,
    ``FourRowTradeoff.overlap_le_product,
    ``FourRowTradeoff.overlap_le_four_collision,
    ``FourRowTradeoff.symEnergy_identity,
    ``FourRowTradeoff.altEnergy_identity,
    ``FourRowTradeoff.sharpConstant_nonneg,
    ``FourRowTradeoff.pair_bound,
    ``FourRowTradeoff.permEnum,
    ``FourRowTradeoff.permEnum_bijective,
    ``FourRowTradeoff.sum_perms,
    ``FourRowTradeoff.shuffleSign,
    ``FourRowTradeoff.permanent_laplace,
    ``FourRowTradeoff.det_laplace,
    ``FourRowTradeoff.sym_complement_energy,
    ``FourRowTradeoff.alt_complement_energy,
    ``FourRowTradeoff.permanent_sq_bound,
    ``FourRowTradeoff.det_sq_bound,
    ``FourRowTradeoff.rowNorm,
    ``FourRowTradeoff.rowProduct,
    ``FourRowTradeoff.rowNorm_nonneg,
    ``FourRowTradeoff.rowNorm_sq,
    ``FourRowTradeoff.rowNorm_semantics,
    ``FourRowTradeoff.rowProduct_nonneg,
    ``FourRowTradeoff.rowProduct_sq,
    ``FourRowTradeoff.weighted_sqrt_cauchy,
    ``FourRowTradeoff.weighted_laplace_bound,
    ``FourRowTradeoff.matrix_tradeoff,
    ``FourRowTradeoff.sharp_four_row,
    ``FourRowTradeoff.flatMatrix,
    ``FourRowTradeoff.oddMatrix,
    ``FourRowTradeoff.flat_permanent,
    ``FourRowTradeoff.flat_det,
    ``FourRowTradeoff.flat_rowProduct,
    ``FourRowTradeoff.one_rowProduct,
    ``FourRowTradeoff.odd_permanent,
    ``FourRowTradeoff.odd_det,
    ``FourRowTradeoff.odd_rowProduct,
    ``FourRowTradeoff.matrix_bound_iff,
    ``FourRowTradeoff.matrix_attainment,
    ``FourRowTradeoff.pencil_bound,
    ``FourRowTradeoff.flat_pencil,
    ``FourRowTradeoff.one_pencil,
    ``FourRowTradeoff.odd_pencil,
    ``FourRowTradeoff.pencil_bound_iff,
    ``FourRowTradeoff.pencilValues,
    ``FourRowTradeoff.pencil_attainment,
    ``FourRowTradeoff.pencil_norm_isGreatest,
    ``FourRowTradeoff.exact_real_pencil_norm,
    ``FourRowTradeoff.tradeoffValues,
    ``FourRowTradeoff.tradeoff_isGreatest,
    ``FourRowTradeoff.exact_tradeoff_norm]
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
