import ArithmeticSupplyWeakMain
import StockAxiomSnapshot
open Lean Elab Command
run_cmd do
  let current ← match IndependentStockAxiomSnapshot.snapshot ((← getEnv).setExporting false) with
    | .ok value => pure value
    | .error error => throwError "{error}"
  let reference ← liftIO <| IO.FS.readFile "stock-standard-axioms.json"
  let expected ← match Json.parse reference with
    | .ok value => pure value
    | .error error => throwError "Invalid stock axiom baseline: {error}"
  unless current == expected do throwError "A standard axiom type or universe declaration differs from stock Lean"
  liftIO <| IO.FS.writeFile "literal-standard-axioms.json" (current.pretty ++ "\n")
  liftIO <| IO.println "STANDARD_AXIOM_TYPES_EXACT_STOCK=true"
