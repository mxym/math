import Mxym
import Lean

open Lean Elab Command Meta

set_option pp.all true
set_option format.width 240
set_option pp.maxSteps 1000000

run_cmd do
  let env := (← getEnv).setExporting false
  let mut selected : Array (Name × ConstantInfo × Name) := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let modName := env.header.moduleNames[idx.toNat]!
      if modName.toString.startsWith "Mxym" ||
          modName.toString.startsWith "OAI.Geometry.ProjectionVolume" ||
          modName.toString.startsWith "Entry005" then
        selected := selected.push (n, ci, modName)
  selected := selected.qsort (fun a b => Name.lt a.1 b.1)
  let mut theoremCount : Nat := 0
  let mut axiomCount : Nat := 0
  for (n, ci, modName) in selected do
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | _ => "other"
    if kind == "theorem" then theoremCount := theoremCount + 1
    if kind == "axiom" then axiomCount := axiomCount + 1
    let typeFmt ← liftTermElabM do ppExpr ci.type
    let axs ← collectAxioms n
    let j := Json.mkObj [
      ("name", toJson n.toString),
      ("module", toJson modName.toString),
      ("kind", toJson kind),
      ("unsafe", toJson ci.isUnsafe),
      ("partial", toJson ci.isPartial),
      ("private", toJson (privateToUserName? n).isSome),
      ("internal_detail", toJson n.isInternalDetail),
      ("equation", toJson (← liftCoreM <| isEqnThm n)),
      ("type", toJson typeFmt.pretty),
      ("axioms", toJson (axs.map Name.toString))]
    logInfo m!"{j.compress}"
  logInfo m!"INDEPENDENT_DECLARATION_COUNTS all={selected.size} theorems={theoremCount} axioms={axiomCount}"
  -- Traverse checked constant types/bodies directly, without the imported axiom summary cache.
  let mut pending : Array Name := selected.filterMap (fun (n, ci, _) => if ci.isUnsafe || ci.isPartial then none else some n)
  let mut seen : NameSet := {}
  let mut reachableAxioms : NameSet := {}
  let mut reachableUnsafe : NameSet := {}
  let mut missing : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.checked.get.find? n then
      if ci.isUnsafe || ci.isPartial then reachableUnsafe := reachableUnsafe.insert n
      if let .axiomInfo _ := ci then reachableAxioms := reachableAxioms.insert n
      for used in ci.type.getUsedConstants do pending := pending.push used
      match ci with
      | .thmInfo v => for used in v.value.getUsedConstants do pending := pending.push used
      | .defnInfo v => for used in v.value.getUsedConstants do pending := pending.push used
      | .opaqueInfo v => for used in v.value.getUsedConstants do pending := pending.push used
      | .inductInfo v => for ctor in v.ctors do pending := pending.push ctor
      | _ => pure ()
    else
      missing := missing.insert n
  let summary := Json.mkObj [
    ("body_traversal_constants", toJson seen.toArray.size),
    ("axioms", toJson (reachableAxioms.toArray.map Name.toString)),
    ("unsafe_or_partial", toJson (reachableUnsafe.toArray.map Name.toString)),
    ("missing_constants", toJson (missing.toArray.map Name.toString))]
  logInfo m!"INDEPENDENT_BODY_TRAVERSAL {summary.compress}"
  if !reachableUnsafe.isEmpty || !missing.isEmpty then throwError "Unsafe or missing kernel dependencies"
  for ax in reachableAxioms.toArray do
    if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
      throwError "Unpermitted direct axiom: {ax}"
