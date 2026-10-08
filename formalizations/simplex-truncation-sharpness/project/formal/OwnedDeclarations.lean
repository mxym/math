import Entry005
import Lean

/- Diagnostic enumeration only: this command supplies no mathematical proof term. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let isOwned := (env.getModuleIdxFor? name).any fun idx =>
      let ownerModule := env.header.moduleNames[idx.toNat]!
      (`Entry005).isPrefixOf ownerModule || (`Mxym.StochasticRigidity).isPrefixOf ownerModule
    if isOwned then
      names := names.push name
  for name in names.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"OWNED_DECL {name}"
