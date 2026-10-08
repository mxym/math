import Entry002.ArithmeticSplittingTower
import Lean

open Lean Elab Command

private def owned (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    let modName := env.header.moduleNames[idx.toNat]!
    modName.toString == "Entry002.ArithmeticSplittingTower"

private def namesJson (ns : Array Name) : Json :=
  toJson ((ns.qsort Name.lt).map Name.toString)

private def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private partial def dependencyClosure (env : Environment) (todo : List Name)
    (cache : NameMap (List Name)) (seen : NameHashSet := {}) :
    NameHashSet × NameMap (List Name) :=
  match todo with
  | [] => (seen, cache)
  | n :: rest =>
    if seen.contains n then dependencyClosure env rest cache seen else
    let seen := seen.insert n
    let (deps, cache) := match cache.find? n with
      | some deps => (deps, cache)
      | none =>
        let deps := (env.find? n).map (fun ci => ci.getUsedConstantsAsSet.toList) |>.getD []
        (deps, cache.insert n deps)
    dependencyClosure env (deps ++ rest) cache seen

run_cmd do
  let env := (← getEnv).setExporting false
  logInfo s!"MODULES_JSON={Json.compress (toJson (env.header.moduleNames.filter (fun n => n.toString.startsWith "Entry002") |>.map Name.toString))}"
  let mut ownedNames : NameHashSet := {}
  for (n, _) in env.constants.toList do
    if owned env n then ownedNames := ownedNames.insert n
  let inventory := env.constants.toList.filterMap fun (n, ci) =>
    if ownedNames.contains n then some <| Json.mkObj [
      ("name", toJson n.toString), ("kind", toJson (kind ci)),
      ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial)] else none
  logInfo s!"INVENTORY_JSON={Json.compress (toJson inventory)}"
  let targets := env.constants.toList.filterMap fun (n, ci) =>
    if ownedNames.contains n && (ci.isTheorem || ci.isDefinition) && !ci.isUnsafe && !ci.isPartial then some n else none
  let mut rows : Array Json := #[]
  let mut cache : NameMap (List Name) := {}
  for n in targets.toArray.qsort Name.lt do
    let some ci := env.find? n | throwError "missing owned declaration {n}"
    let direct := ci.getUsedConstantsAsSet.toList.toArray
    let (closure, updatedCache) := dependencyClosure env [n] cache
    cache := updatedCache
    let all := closure.toArray
    let ax := all.filter fun n => (env.find? n).any ConstantInfo.isAxiom
    let unsafeDeps := all.filter fun n => (env.find? n).any ConstantInfo.isUnsafe
    let missing := all.filter fun n => (env.find? n).isNone
    let partials := all.filter fun n => (env.find? n).any ConstantInfo.isPartial
    let computed ← collectAxioms n
    let typename ← liftTermElabM <| Meta.ppExpr ci.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString), ("kind", toJson (kind ci)),
      ("type", toJson typename.pretty),
      ("direct_owned", namesJson (direct.filter ownedNames.contains)),
      ("direct_external", namesJson (direct.filter (fun n => !ownedNames.contains n))),
      ("transitive_count", toJson all.size),
      ("transitive_owned", namesJson (all.filter ownedNames.contains)),
      ("body_traversal_axioms", namesJson ax),
      ("collectAxioms", namesJson computed),
      ("unsafe_dependencies", namesJson unsafeDeps),
      ("partial_dependencies", namesJson partials),
      ("missing_dependencies", namesJson missing)]
  logInfo s!"DEPENDENCY_JSON={Json.compress (toJson rows)}"
