import Entry005
import Lean

/- Diagnostic audit only: these commands supply no mathematical proof term.
The sole disabled linter warns about inspecting Lean-generated auxiliary names;
all kernel checks remain enabled. Every inspected name comes from the actual environment. -/
set_option linter.auxLemma false
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
    elabCommand (← `(#print axioms $(mkIdent name)))
