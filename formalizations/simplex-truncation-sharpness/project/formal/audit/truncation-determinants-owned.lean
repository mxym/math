import Entry005.TruncationScalarCancellation
import Lean

/- Diagnostic only. All mathematical proof terms retain ordinary kernel checking. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let owned := (env.getModuleIdxFor? name).any fun idx =>
      let owner := env.header.moduleNames[idx.toNat]!
      owner == `Entry005.TruncationFacetDeterminants ||
        owner == `Entry005.TruncationScalarCancellation
    if owned then names := names.push name
  for name in names.qsort (fun a b => a.toString < b.toString) do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound
    unless bad.isEmpty do
      throwError "Unallowed module-owned axiom for {name}: {bad}"
    logInfo m!"OWNED_DECL {name}"
    logInfo m!"OWNED_AXIOMS {name}: {axioms}"

#check Entry005.truncation_packed_horizontal_tuple_sum
#check Entry005.truncation_packed_lifted_tuple_sum
#check Entry005.truncation_scalar_cancellation
