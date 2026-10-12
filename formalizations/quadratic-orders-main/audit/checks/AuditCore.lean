import Lean

/- Independent replay auditor. It only inspects the already imported environment.
   Logical declarations in the mathematical project do not import this tool. -/
open Lean Elab Command

namespace IndependentAudit

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def moduleName? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def belongs (env : Environment) (modules : Array Name) (n : Name) : Bool :=
  (moduleName? env n).any modules.contains

def safeLogicalRoot (ci : ConstantInfo) : Bool :=
  (ci.isTheorem || ci.isDefinition || kind ci == "opaque") && !ci.isUnsafe && !ci.isPartial

/-- Construct edges explicitly from stored type/value and generated family metadata.
    Uses the compiler's expression constant visitor, not its axiom cache. -/
def storedEdges (ci : ConstantInfo) : NameSet := Id.run do
  let mut result := ci.type.getUsedConstantsAsSet
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ value.getUsedConstantsAsSet
  else
    match ci with
    | .inductInfo info =>
      for ctor in info.ctors do result := result.insert ctor
    | .ctorInfo info => result := result.insert info.name
    | .recInfo info =>
      for family in info.all do result := result.insert family
    | _ => pure ()
  return result

structure TraversalCache where
  direct : NameMap (List Name) := {}
  edgeDisagreements : NameHashSet := {}

/-- Each root gets a fresh visited set. Only direct adjacency is cached across roots. -/
partial def closure (env : Environment) (todo : List Name)
    (memo : TraversalCache) (seen : NameHashSet := {}) : NameHashSet × TraversalCache :=
  match todo with
  | [] => (seen, memo)
  | n :: rest =>
    if seen.contains n then closure env rest memo seen else
    let (next, memo) := match memo.direct.find? n with
      | some ns => (ns, memo)
      | none =>
        let edges := (env.find? n).map storedEdges |>.getD {}
        let officialEdges := (env.find? n).map ConstantInfo.getUsedConstantsAsSet |>.getD {}
        let same := edges.toList == officialEdges.toList
        (edges.toList, { memo with
          direct := memo.direct.insert n edges.toList
          edgeDisagreements := if same then memo.edgeDisagreements else memo.edgeDisagreements.insert n })
    closure env (next ++ rest) memo (seen.insert n)

def namesJson (ns : Array Name) : Json :=
  toJson ((ns.qsort Name.lt).map Name.toString)

def runAudit (modules : Array Name) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throwError "Expected owned module was not imported: {mod}"
  let unexpected := env.header.moduleNames.filter fun mod =>
    (mod == `Entry002 || mod.toString.startsWith "Entry002.") && !modules.contains mod
  -- For a negative-control run Entry002 is not imported at all.
  unless unexpected.isEmpty do throwError "Unlisted Entry002 modules: {unexpected}"
  let declarations := env.constants.toList.filter fun (n, _) => belongs env modules n
  let ownedNames := declarations.foldl (fun acc (n, _) => acc.insert n) ({} : NameHashSet)
  let inventory := declarations.map fun (n, ci) => Json.mkObj [
    ("name", toJson n.toString), ("module", toJson ((moduleName? env n).map Name.toString)),
    ("kind", toJson (kind ci)), ("safe_root", toJson (safeLogicalRoot ci)),
    ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial)]
  let mut paths : Array Json := #[]
  for mod in env.header.moduleNames do
    let path ← liftIO (Lean.findOLean mod)
    paths := paths.push <| Json.mkObj [("module", toJson mod.toString), ("path", toJson path.toString)]
  liftIO <| IO.println s!"RESOLVED_PATHS_JSON={Json.compress (toJson paths)}"
  liftIO <| IO.println s!"OWNED_MODULES_JSON={Json.compress (toJson (modules.map Name.toString))}"
  liftIO <| IO.println s!"INVENTORY_JSON={Json.compress (toJson inventory)}"
  let mut memo : TraversalCache := {}
  for n in ownedNames.toArray.qsort Name.lt do
    let some ci := env.find? n | throwError "Owned constant missing: {n}"
    let direct := (storedEdges ci).toList.toArray
    let (seen, updated) := closure env [n] memo
    memo := updated
    let reachable := seen.toArray
    let cached ← collectAxioms n
    let typeText ← liftTermElabM <| Meta.ppExpr ci.type
    let row := Json.mkObj [
      ("name", toJson n.toString), ("module", toJson ((moduleName? env n).map Name.toString)),
      ("kind", toJson (kind ci)), ("safe_root", toJson (safeLogicalRoot ci)),
      ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
      ("type", toJson typeText.pretty),
      ("direct_owned", namesJson (direct.filter ownedNames.contains)),
      ("direct_external", namesJson (direct.filter fun k => !ownedNames.contains k)),
      ("transitive_count", toJson reachable.size),
      ("transitive_owned", namesJson (reachable.filter ownedNames.contains)),
      ("body_traversal_axioms", namesJson (reachable.filter fun k => (env.find? k).any ConstantInfo.isAxiom)),
      ("collectAxioms", namesJson cached),
      ("unsafe_dependencies", namesJson (reachable.filter fun k => (env.find? k).any ConstantInfo.isUnsafe)),
      ("partial_dependencies", namesJson (reachable.filter fun k => (env.find? k).any ConstantInfo.isPartial)),
      ("missing_dependencies", namesJson (reachable.filter fun k => (env.find? k).isNone))]
    liftIO <| IO.println s!"OWNED_ROW_JSON={Json.compress row}"
  liftIO <| IO.println s!"EDGE_EXTRACTOR_DISAGREEMENTS_JSON={Json.compress (namesJson memo.edgeDisagreements.toArray)}"
  liftIO <| IO.println s!"REACHABLE_CONSTANT_COUNT={memo.direct.size}"
  liftIO <| IO.println "AUDIT_COMPLETED=true"

end IndependentAudit
