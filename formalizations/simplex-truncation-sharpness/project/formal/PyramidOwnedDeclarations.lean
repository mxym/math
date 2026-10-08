import Entry005.PyramidFormalization
import Lean

/- Diagnostic enumeration; it produces no mathematical proof term. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let isOwned := (env.getModuleIdxFor? name).any fun idx =>
      let owner := env.header.moduleNames[idx.toNat]!
      (`Entry005).isPrefixOf owner || (`Mxym).isPrefixOf owner || (`OAI).isPrefixOf owner
    if isOwned then names := names.push name
  for name in names.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"OWNED_DECL {name}"
