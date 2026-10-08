import Entry005.TruncationFormalization
import Lean

/- Diagnostic only: enumerate actual declaring modules, including private and
generated declarations, using Lean's same collector as `#print axioms`.
No diagnostic evaluation supplies a theorem proof. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let owned := (env.getModuleIdxFor? name).any fun idx =>
      let owner := env.header.moduleNames[idx.toNat]!
      (`Entry005).isPrefixOf owner || (`Mxym).isPrefixOf owner || (`OAI).isPrefixOf owner
    if owned then names := names.push name
  for name in names.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"OWNED_DECL {name}"
    let axioms ← collectAxioms name
    logInfo m!"OWNED_AXIOMS {name}: {axioms.toList}"
    if let some info := env.find? name then
      if info.isTheorem && !name.isInternal then
        if let some idx := env.getModuleIdxFor? name then
          logInfo m!"PUBLIC_THEOREM {env.header.moduleNames[idx.toNat]!} {name}"
