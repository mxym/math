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
    ``HydrologyTree.repeatedBlock,
    ``HydrologyTree.repeatedBlock_apply,
    ``HydrologyTree.toMatrix_repeatedBlock,
    ``HydrologyTree.det_repeatedBlock,
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
    ``HydrologyTree.gluingJacobian_eq_resultant_sq]
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
