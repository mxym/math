import Lean

open Lean

namespace StandardAxiomGuard

/- Expected expressions are constructed from the pinned upstream signatures.
No expected type is copied from the loaded environment. Bound variables use
de Bruijn indices. Only binder names and universe-parameter names are normalized;
binder visibility and the complete expression structure remain significant. -/

def expectedPropext : Expr :=
  .forallE `a (.sort .zero)
    (.forallE `b (.sort .zero)
      (.forallE `_ (mkApp2 (.const `Iff []) (.bvar 1) (.bvar 0))
        (mkApp3 (.const `Eq [.succ .zero]) (.sort .zero) (.bvar 2) (.bvar 1))
        .default) .implicit) .implicit

def expectedChoice : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `_ (mkApp (.const `Nonempty [.param `u]) (.bvar 0))
      (.bvar 1) .default) .implicit

def expectedQuotSound : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r
      (.forallE `_ (.bvar 0) (.forallE `_ (.bvar 1) (.sort .zero) .default) .default)
      (.forallE `a (.bvar 1)
        (.forallE `b (.bvar 2)
          (.forallE `_ (mkApp2 (.bvar 2) (.bvar 1) (.bvar 0))
            (mkApp3 (.const `Eq [.param `u])
              (mkApp2 (.const `Quot [.param `u]) (.bvar 4) (.bvar 3))
              (mkApp3 (.const `Quot.mk [.param `u]) (.bvar 4) (.bvar 3) (.bvar 2))
              (mkApp3 (.const `Quot.mk [.param `u]) (.bvar 4) (.bvar 3) (.bvar 1)))
            .default) .implicit) .implicit) .implicit) .implicit

def expected? (name : Name) : Option (List Name × Expr) :=
  if name == `propext then some ([], expectedPropext)
  else if name == `Classical.choice then some ([`u], expectedChoice)
  else if name == `Quot.sound then some ([`u], expectedQuotSound)
  else none

def normalizeLevel (params : List Name) : Level → Option Level
  | .zero => some .zero
  | .succ u => return .succ (← normalizeLevel params u)
  | .max u v => return .max (← normalizeLevel params u) (← normalizeLevel params v)
  | .imax u v => return .imax (← normalizeLevel params u) (← normalizeLevel params v)
  | .param n =>
    if params.contains n then some (.param (.num `u (params.idxOf n))) else none
  | .mvar _ => none

/-- Reject all expression forms absent from the three closed standard signatures.
In particular, no free/metavariables, expression metadata, lets or reductions. -/
def normalizeType (params : List Name) : Expr → Option Expr
  | .sort u => return .sort (← normalizeLevel params u)
  | .bvar i => some (.bvar i)
  | .const n us => return .const n (← us.mapM (normalizeLevel params))
  | .app f a => return .app (← normalizeType params f) (← normalizeType params a)
  | .forallE _ d b bi =>
    return .forallE .anonymous (← normalizeType params d) (← normalizeType params b) bi
  | _ => none

def validate (ci : ConstantInfo) : Except String Unit := do
  let some (params, ty) := expected? ci.name
    | throw s!"UNEXPECTED_AXIOM_NAME {ci.name}"
  unless ci.isAxiom && !ci.isUnsafe && !ci.isPartial do
    throw s!"AXIOM_KIND_OR_SAFETY_MISMATCH {ci.name}"
  unless ci.levelParams.length == params.length && ci.levelParams.Nodup do
    throw s!"AXIOM_UNIVERSE_PARAMETERS_MISMATCH {ci.name}"
  let some actual := normalizeType ci.levelParams ci.type
    | throw s!"AXIOM_INVALID_TYPE_SYNTAX {ci.name}"
  let some expected := normalizeType params ty
    | throw s!"INVALID_EXPECTED_SIGNATURE {ci.name}"
  unless Expr.equal actual expected do
    throw s!"AXIOM_SIGNATURE_MISMATCH {ci.name}"

def validateEnvironment (env : Environment) : Except String Unit := do
  for n in [`propext, `Classical.choice, `Quot.sound] do
    let some ci := env.find? n | throw s!"STANDARD_AXIOM_MISSING {n}"
    validate ci

def exportJson (env : Environment) : Elab.Command.CommandElabM Json := do
  let mut result : Array Json := #[]
  for n in [`propext, `Classical.choice, `Quot.sound] do
    let some ci := env.find? n | throwError "STANDARD_AXIOM_MISSING {n}"
    let some (params, expected) := expected? n | throwError "missing specification"
    let actualPP ← Elab.Command.liftTermElabM do
      return (← Meta.ppExpr ci.type).pretty
    result := result.push <| Json.mkObj [
      ("name", toJson n.toString), ("is_axiom", toJson ci.isAxiom),
      ("is_unsafe", toJson ci.isUnsafe), ("is_partial", toJson ci.isPartial),
      ("level_params", toJson (ci.levelParams.map Name.toString)),
      ("actual_type_full", toJson actualPP),
      ("actual_type_raw", toJson (reprStr ci.type)),
      ("expected_type_raw", toJson (reprStr expected)),
      ("normalized_actual_raw", toJson (reprStr (normalizeType ci.levelParams ci.type))),
      ("normalized_expected_raw", toJson (reprStr (normalizeType params expected))),
      ("validation", toJson (reprStr (validate ci)))]
  return Json.arr result

end StandardAxiomGuard
