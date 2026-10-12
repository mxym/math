import Lean.Replay
import Lean
open Lean Elab Command

partial def controlClosure (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : Except String (Std.HashMap Name ConstantInfo) :=
  match todo with
  | [] => .ok seen
  | n :: rest =>
    if seen.contains n then controlClosure env rest seen
    else match env.find? n with
    | none => .error s!"Missing control dependency {n}"
    | some ci =>
      let extra := match ci with
        | .inductInfo v => v.all ++ v.ctors
        | .ctorInfo v => [v.induct]
        | .recInfo v => v.all
        | _ => []
      controlClosure env (extra ++ ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n ci)

run_cmd do
  let env := (← getEnv).setExporting false
  let cs ← match controlClosure env [``True.intro, ``False] {} with
    | .ok cs => pure cs
    | .error msg => throwError msg
  let base ← mkEmptyEnvironment 0
  let positive : ConstantInfo := .thmInfo {
    name := `ReplayControlPositive, levelParams := [],
    type := mkConst ``True, value := mkConst ``True.intro }
  let verified ← base.toKernelEnv.replay (cs.insert `ReplayControlPositive positive)
  unless (verified.find? `ReplayControlPositive).isSome do
    throwError "Positive replay control was not installed"
  let negative : ConstantInfo := .thmInfo {
    name := `ReplayControlNegative, levelParams := [],
    type := mkConst ``False, value := mkConst ``True.intro }
  let rejected ← try
    let _ ← base.toKernelEnv.replay (cs.insert `ReplayControlNegative negative)
    pure false
  catch _ => pure true
  unless rejected do throwError "Invalid proof was accepted by trust-zero replay"
  logInfo "REPLAY_POSITIVE_CONTROL_PASS"
  logInfo "REPLAY_NEGATIVE_CONTROL_REJECTED: True.intro is not a proof of False"
