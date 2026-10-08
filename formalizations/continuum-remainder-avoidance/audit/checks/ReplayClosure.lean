import ContinuumGeometric
import ContinuumRemainder
import Lean.Replay
import Lean

open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Recheck the stored proof and all referenced library declarations in a new
-- trust-level-zero kernel environment, rather than trusting imported oleans.
partial def gather (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : Std.HashMap Name ConstantInfo :=
  match todo with
  | [] => seen
  | n :: todo =>
    if seen.contains n then gather env todo seen
    else match env.find? n with
    | none => gather env todo seen
    | some ci =>
      let extra := match ci with
        | .inductInfo v => v.all ++ v.ctors
        | .ctorInfo v => [v.induct]
        | .recInfo v => v.all
        | _ => []
      gather env (extra ++ ci.getUsedConstantsAsSet.toList ++ todo) (seen.insert n ci)

run_cmd do
  let env := (← getEnv).setExporting false
  let root := ``ContinuumRemainder.continuum_power_target
  let cs := gather env [root, ``ContinuumRemainder.compact_power_avoidance, ``ContinuumRemainder.robustCompactBlockerSpec_proved] {}
  for (n, ci) in cs.toList do
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial replay node {n}"
    if ci.isAxiom then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected replay axiom {n}"
  logInfo m!"REPLAY_BEGIN {cs.size} declarations; trust level zero; empty kernel environment"
  let base ← mkEmptyEnvironment 0
  let verified ← base.toKernelEnv.replay cs
  let some ci := verified.find? root | throwError "Root absent after replay"
  unless ci.type == Expr.const ``ContinuumRemainder.ContinuumPowerTarget [] do
    throwError "Root type mismatch after replay"
  for r in [root, ``ContinuumRemainder.compact_power_avoidance, ``ContinuumRemainder.robustCompactBlockerSpec_proved] do
    let some original := env.find? r | throwError "Original root absent {r}"
    let some checked := verified.find? r | throwError "Replayed root absent {r}"
    unless original.type == checked.type && original.levelParams == checked.levelParams do
      throwError "Root type/levels changed {r}"
  logInfo m!"EMPTY_KERNEL_REPLAY_PASS {cs.size} declarations"
