import BapatN200Counterexample
import StandardAxiomGuard
import Lean

open Lean Elab Command
set_option pp.all true

#print propext
#print Classical.choice
#print Quot.sound

run_cmd do
  let env := (← getEnv).setExporting false
  match StandardAxiomGuard.validateEnvironment env with
  | .error e => throwError "{e}"
  | .ok _ => pure ()
  let some output ← IO.getEnv "STANDARD_AXIOM_OUTPUT"
    | throwError "STANDARD_AXIOM_OUTPUT required"
  IO.FS.writeFile output (← StandardAxiomGuard.exportJson env).pretty
  let mut rejected := 0
  for n in [``propext, ``Classical.choice, ``Quot.sound] do
    let some (.axiomInfo v) := env.find? n | throwError "missing axiom {n}"
    let mutations : List (String × ConstantInfo) := [
      ("wrong type False", .axiomInfo {v with type := mkConst ``False}),
      ("extra universe", .axiomInfo {v with levelParams := v.levelParams ++ [`extra]}),
      ("unsafe flag", .axiomInfo {v with isUnsafe := true}),
      ("wrong kind", .thmInfo {name := v.name, levelParams := v.levelParams, type := v.type, value := mkConst ``True.intro})]
    for (label, bad) in mutations do
      match StandardAxiomGuard.validate bad with
      | .ok _ => throwError "NEGATIVE_CONTROL_ACCEPTED {n}: {label}"
      | .error reason =>
        rejected := rejected + 1
        logInfo m!"SIGNATURE_NEGATIVE_REJECTED {n}: {label}: {reason}"
  let some (.axiomInfo v) := env.find? ``propext | throwError "missing propext"
  let .forallE nm d b _ := v.type | throwError "unexpected outer binder"
  match StandardAxiomGuard.validate (.axiomInfo {v with type := .forallE nm d b .default}) with
  | .ok _ => throwError "BINDER_VISIBILITY_MUTATION_ACCEPTED"
  | .error reason =>
    rejected := rejected + 1
    logInfo m!"SIGNATURE_NEGATIVE_REJECTED binder visibility: {reason}"
  unless rejected == 13 do throwError "NEGATIVE_COUNT_MISMATCH"
  logInfo m!"STANDARD_AXIOM_SIGNATURES_PASS; 3 actual declarations; 13 negative controls rejected"
