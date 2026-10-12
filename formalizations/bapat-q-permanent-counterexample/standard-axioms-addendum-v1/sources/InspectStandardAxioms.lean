import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
  let env := (← getEnv).setExporting false
  for n in [``propext, ``Classical.choice, ``Quot.sound] do
    let some ci := env.find? n | throwError "missing {n}"
    logInfo m!"NAME {n}; LEVELS {repr ci.levelParams}; AXIOM {ci.isAxiom}"
    logInfo m!"RAW {repr ci.type}"
    logInfo m!"TYPE {ci.type}"
