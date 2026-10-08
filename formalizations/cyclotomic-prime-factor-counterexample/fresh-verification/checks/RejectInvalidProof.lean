import Lean
import Lean.Replay

open Lean Elab Command
set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let names := [``False, ``True, ``True.intro]
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for n in names do
    let some ci := env.find? n | throwError "Missing negative-control dependency {n}"
    constants := constants.insert n ci
  let bad : ConstantInfo := .thmInfo {
    name := `IndependentNegativeControl.invalidFalse
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  constants := constants.insert bad.name bad
  let base ← mkEmptyEnvironment 0
  let outcome ← try
    let _ ← base.toKernelEnv.replay constants
    pure (none : Option String)
  catch e => pure (some (← e.toMessageData.toString))
  match outcome with
  | none => throwError "NEGATIVE_CONTROL_FAILED: invalid proof accepted"
  | some message =>
    unless message.contains "type mismatch" do
      throwError "NEGATIVE_CONTROL_WRONG_FAILURE: {message}"
    logInfo m!"INVALID_PROOF_REJECTED_BY_EMPTY_TRUST_ZERO_KERNEL\n{message}"
