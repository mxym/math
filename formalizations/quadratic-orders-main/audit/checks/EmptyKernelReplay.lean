import Lean.Replay
import AuditCore

/- An audit tool only. The mathematical project does not import this module.
   Each replay starts with mkEmptyEnvironment 0, accepts only the three standard
   axioms, and uses official Lean.Kernel.Environment.replay with kernel checks.
   No imported declaration is seeded into the destination environment. -/
open Lean Elab Command

namespace IndependentEmptyReplay

partial def saturate (source : Environment) (todo : List Name)
    (seen : NameHashSet := {}) : IO NameHashSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← saturate source rest seen
    let some ci := source.find? n | throw <| IO.userError s!"Missing source declaration {n}"
    let mut edges := IndependentAudit.storedEdges ci
    -- Official replay reconstructs a whole mutual inductive block at once.
    if let .inductInfo info := ci then
      for member in info.all do edges := edges.insert member
    return ← saturate source (edges.toList ++ rest) (seen.insert n)

def run (roots : Array Name) (resultPath : String) (corruptRoot := false) : CommandElabM Unit := do
  let source := (← getEnv).setExporting false
  let started ← liftIO IO.monoMsNow
  let names ← liftIO <| saturate source roots.toList
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut selected : Std.HashMap Name ConstantInfo := {}
  let mut axioms : Array Name := #[]
  for n in names.toArray do
    let some ci := source.find? n | throwError "Missing selected constant {n}"
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial selected constant {n}"
    if ci.isAxiom then
      unless allowed.contains n do throwError "Unexpected axiom {n}"
      axioms := axioms.push n
    selected := selected.insert n ci
  -- The negative control changes a stored proof to an ill-typed term. It must
  -- be rejected by the new kernel, rather than only by a source-token scanner.
  if corruptRoot then
    let n := roots[0]!
    let some (.thmInfo info) := selected[n]? | throwError "Control root is not a theorem"
    selected := selected.insert n (.thmInfo { info with value := mkConst `Nat.zero })
  let empty ← liftIO <| mkEmptyEnvironment 0
  unless empty.constants.toList.isEmpty do throwError "Replay destination is not empty"
  unless empty.header.trustLevel == 0 do throwError "Replay trust level is not zero"
  let startRecord := Json.mkObj [
    ("status", toJson ("running" : String)),
    ("roots", toJson (roots.map Name.toString)),
    ("source_closure_constants", toJson names.size),
    ("initial_destination_constants", toJson (0 : Nat)),
    ("trust_level", toJson (0 : Nat)),
    ("axioms", IndependentAudit.namesJson axioms),
    ("corrupted_proof_control", toJson corruptRoot)]
  liftIO <| IO.FS.writeFile resultPath (startRecord.pretty ++ "\n")
  liftIO <| IO.FS.writeFile (resultPath ++ ".closure.json")
    ((IndependentAudit.namesJson names.toArray).pretty ++ "\n")
  let checked ← liftIO <| empty.toKernelEnv.replay selected
  for n in names.toArray do
    unless (checked.find? n).isSome do throwError "Replayed constant absent: {n}"
  for n in roots do
    let some expected := source.find? n | throwError "Source root absent {n}"
    let some actual := checked.find? n | throwError "Destination root absent {n}"
    unless actual.type == expected.type do throwError "Root type changed: {n}"
  let finished ← liftIO IO.monoMsNow
  let record := Json.mkObj [
    ("status", toJson ("PASS" : String)),
    ("roots", toJson (roots.map Name.toString)),
    ("source_closure_constants", toJson names.size),
    ("initial_destination_constants", toJson (0 : Nat)),
    ("trust_level", toJson (0 : Nat)),
    ("axioms", IndependentAudit.namesJson axioms),
    ("elapsed_ms", toJson (finished-started)),
    ("corrupted_proof_control", toJson corruptRoot),
    ("method", toJson ("Official Lean 4.34.1 Kernel.Environment.replay into mkEmptyEnvironment 0; no loaded constants in destination" : String))]
  liftIO <| IO.FS.writeFile resultPath (record.pretty ++ "\n")
  liftIO <| IO.println s!"EMPTY_KERNEL_REPLAY={Json.compress record}"

end IndependentEmptyReplay
