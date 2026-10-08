import RealPowerBridge
import Lean.Replay
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
partial def gather (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : Except String (Std.HashMap Name ConstantInfo) :=
  match todo with
  | [] => .ok seen
  | n :: todo =>
    if seen.contains n then gather env todo seen
    else match env.find? n with
    | none => .error s!"Missing referenced declaration {n}"
    | some ci =>
      let extra := match ci with
        | .inductInfo v => v.all ++ v.ctors
        | .ctorInfo v => [v.induct]
        | .recInfo v => v.all
        | _ => []
      gather env (extra ++ ci.getUsedConstantsAsSet.toList ++ todo) (seen.insert n ci)
run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array String := #["RealPowerBridge"]
  let mut roots : Array Name := #[]
  let mut skipped : Array String := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if modules.contains env.header.moduleNames[idx.toNat]!.toString then
        if ci.isUnsafe || ci.isPartial then skipped := skipped.push n.toString
        else roots := roots.push n
  unless skipped.isEmpty do throwError "Owned unsafe or partial constants: {skipped}"
  for n in roots do
    let axs ← collectAxioms n
    unless axs.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "Unexpected owned axiom dependency {n}: {axs}"
    logInfo m!"OWNED_AXIOMS {n} = {axs}"
  unless roots.contains ``EntropyCounterexample.wakhare_conjecture_two_false_original_real_power do
    throwError "Actual original real-power final theorem absent from replay roots"
  let cs ← match gather env roots.toList {} with
    | .ok cs => pure cs
    | .error err => throwError "{err}"
  for (n, ci) in cs.toList do
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial replay node {n}"
    if ci.isAxiom then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected replay axiom {n}"
  logInfo m!"REPLAY_BEGIN roots={roots.size} closure={cs.size} skipped={Json.compress (toJson skipped)} trust=0 empty=true"
  let base ← mkEmptyEnvironment 0
  let verified ← base.toKernelEnv.replay cs
  for r in roots do
    let some original := env.find? r | throwError "Original root absent {r}"
    let some checked := verified.find? r | throwError "Replayed root absent {r}"
    unless original.type == checked.type && original.levelParams == checked.levelParams do
      throwError "Root type/levels changed {r}"
  logInfo m!"ALL_SAFE_OWNED_EMPTY_KERNEL_REPLAY_PASS roots={roots.size} closure={cs.size}"
