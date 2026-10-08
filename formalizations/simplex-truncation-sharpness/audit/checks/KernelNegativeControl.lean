import Lean.Replay
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
partial def gatherControl (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : Std.HashMap Name ConstantInfo :=
  match todo with
  | [] => seen
  | n :: todo =>
    if seen.contains n then gatherControl env todo seen
    else match env.find? n with
    | none => seen
    | some ci =>
      let extra := match ci with
        | .inductInfo v => v.all ++ v.ctors
        | .ctorInfo v => [v.induct]
        | .recInfo v => v.all
        | _ => []
      gatherControl env (extra ++ ci.getUsedConstantsAsSet.toList ++ todo) (seen.insert n ci)
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `DeliberatelyInvalidAuditProof
  let bad : ConstantInfo := .thmInfo {
    name := name
    type := mkConst ``True
    value := mkConst ``Nat.zero
    levelParams := []
    all := [name] }
  let cs := (gatherControl env [``True, ``Nat.zero] {}).insert name bad
  let base ← mkEmptyEnvironment 0
  let rejected ← try
    let _ ← base.toKernelEnv.replay cs
    pure false
  catch e =>
    logInfo m!"EXPECTED_KERNEL_REJECTION: {e.toMessageData}"
    pure true
  unless rejected do throwError "Invalid proof unexpectedly accepted"
  logInfo "KERNEL_NEGATIVE_CONTROL_PASS"
