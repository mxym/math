import Lean.Replay
import Lean

open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace APPTVerification

/-- Audit code only; this is not part of any mathematical theorem. -/
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

/-- Replay an entire proof closure in a trust-zero empty kernel. Then replace
one root proof by True.intro and require a second fresh kernel to reject it. -/
def replayAndCorrupt (roots : List Name) (stem : String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let some corruptRoot := roots.head? | throwError "No roots selected"
  -- Include True.intro explicitly: a missing declaration cannot explain rejection.
  let cs ← match collect env (``True.intro :: roots) {} with
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
  let some ci := cs[corruptRoot]? | throwError "Corruption root missing"
  let bad := match ci with
    | .thmInfo v => ConstantInfo.thmInfo {v with value := mkConst ``True.intro}
    | _ => ci
  unless ci.isTheorem do throwError "Corruption control must select a theorem"
  let badCs := cs.insert corruptRoot bad
  let rejected ← try
    let fresh ← mkEmptyEnvironment 0
    let _ ← fresh.toKernelEnv.replay badCs
    pure false
  catch e =>
    logInfo m!"EXPECTED_KERNEL_REJECTION: {e.toMessageData}"
    pure true
  unless rejected do throwError "Corrupted theorem was accepted by the kernel"
  let names := (cs.toList.map (fun p => p.1.toString)).mergeSort (fun a b => decide (a < b))
  let axioms := (cs.toList.filterMap (fun p => if p.2.isAxiom then some p.1.toString else none)).mergeSort (fun a b => decide (a < b))
  IO.FS.writeFile s!"{stem}-roots.txt" (String.intercalate "\n" (roots.map Name.toString) ++ "\n")
  IO.FS.writeFile s!"{stem}-closure.txt" (String.intercalate "\n" names ++ "\n")
  IO.FS.writeFile s!"{stem}-axioms.txt" (String.intercalate "\n" axioms ++ "\n")
  logInfo m!"EMPTY_KERNEL_REPLAY_PASS {cs.size} declarations; {roots.length} roots; trust level zero"
  logInfo m!"CORRUPTED_PROOF_REJECTED {corruptRoot}"

end APPTVerification
