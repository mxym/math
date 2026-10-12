import Entry005.TruncationFacetGeometry
import Lean

/- Diagnostic only: use Lean's same transitive axiom collector as `#print axioms`,
without referencing generated auxiliary names in elaborated theorem syntax. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array Name := #[`Entry005.TruncationSimplexVolume,
    `Entry005.TruncationVolume, `Entry005.TruncationFacetGeometry]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let owned := (env.getModuleIdxFor? name).any fun idx =>
      modules.contains env.header.moduleNames[idx.toNat]!
    if owned then names := names.push name
  for name in names.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"OWNED_DECL {name}"
    let axioms ← collectAxioms name
    logInfo m!"OWNED_AXIOMS {name}: {axioms.toList}"
