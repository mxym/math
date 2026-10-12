import Lean
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let mut rows : Array Json := #[]
  for n in #[`propext, `Classical.choice, `Quot.sound] do
    let some ci := env.find? n | throwError "Missing standard axiom {n}"
    unless ci.isAxiom do throwError "Standard axiom kind changed: {n}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("level_params", toJson (ci.levelParams.map Name.toString)),
      ("type_repr", toJson (reprStr ci.type))]
  liftIO <| IO.FS.writeFile "stock-standard-axioms.json" ((toJson rows).pretty ++ "\n")
