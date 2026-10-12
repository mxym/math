import Entry005.PyramidFormalization
import Lean

/- Diagnostic inventory of genuine public theorem constants and defining modules. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    let isOwned := (env.getModuleIdxFor? name).any fun idx =>
      let owner := env.header.moduleNames[idx.toNat]!
      (`Entry005).isPrefixOf owner || (`Mxym).isPrefixOf owner || (`OAI).isPrefixOf owner
    if isOwned && info.isTheorem && !name.isInternal then names := names.push name
  for name in names.qsort (fun a b => a.toString < b.toString) do
    let owner := env.header.moduleNames[(env.getModuleIdxFor? name).get!.toNat]!
    logInfo m!"PUBLIC_THEOREM {owner} {name}"
