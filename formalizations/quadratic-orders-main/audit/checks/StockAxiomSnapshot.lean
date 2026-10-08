import Lean
open Lean
namespace IndependentStockAxiomSnapshot
/-- Compiled with stock Lean alone, so expression rendering and axiom checks
are fixed before any mathematical or class-field module is imported. -/
def snapshot (env : Environment) : Except String Json := do
  let mut rows : Array Json := #[]
  for n in #[`propext, `Classical.choice, `Quot.sound] do
    let some ci := env.find? n | throw s!"Missing standard axiom {n}"
    unless ci.isAxiom do throw s!"Standard axiom kind changed: {n}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("level_params", toJson (ci.levelParams.map Name.toString)),
      ("type_repr", toJson (reprStr ci.type))]
  return toJson rows
end IndependentStockAxiomSnapshot
