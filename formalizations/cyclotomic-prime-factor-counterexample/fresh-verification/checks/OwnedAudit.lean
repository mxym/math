import CoefficientList
import CyclotomicFormulas
import PrimeExclusion
import BasicProperties
import Expansion
import DataProperties
import Counterexample
import CenteredCertificate
import BasicPropertiesAudit
import PrimeExclusionAudit
import Audit
import Lean
import Lean.Replay

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.all true

namespace IndependentAudit

def ownedModules : Array String := #[ "CoefficientList", "CyclotomicFormulas", "PrimeExclusion", "BasicProperties", "Expansion", "DataProperties", "Counterexample", "CenteredCertificate", "BasicPropertiesAudit", "PrimeExclusionAudit", "Audit" ]
def requestedRoots : Array Name := #[ ``CyclotomicCounterexample.explicit_counterexample, ``CyclotomicCounterexample.conjecture48_false, ``CyclotomicCounterexample.F_centered_certificate, ``CyclotomicCounterexample.F_qInteger_quotient_certificate ]

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => "<current-or-missing>"

def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def structuralDeps (ci : ConstantInfo) : List Name :=
  match ci with
  | .inductInfo v => v.all ++ v.ctors
  | .ctorInfo v => [v.induct]
  | .recInfo v => v.all
  | .defnInfo v => v.all
  | .thmInfo v => v.all
  | .opaqueInfo v => v.all
  | .quotInfo _ => [``Eq]
  | _ => []

partial def gather (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : IO (Std.HashMap Name ConstantInfo) := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← gather env rest seen
    let some ci := env.find? n | throw <| IO.userError s!"MISSING_CONSTANT {n}"
    gather env (structuralDeps ci ++ ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n ci)

def namesJson (ns : NameSet) : Json :=
  toJson ((ns.toArray.qsort Name.lt).map Name.toString)

def nodeJson (env : Environment) (n : Name) (ci : ConstantInfo) : Json :=
  Json.mkObj [
    ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
    ("kind", toJson (kindOf ci)), ("unsafe", toJson ci.isUnsafe),
    ("partial", toJson ci.isPartial),
    ("type_direct", namesJson ci.type.getUsedConstantsAsSet),
    ("value_direct", namesJson (match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstantsAsSet | none => {})),
    ("structural_dependencies", toJson ((structuralDeps ci).map Name.toString))]

run_cmd do
  let env := (← getEnv).setExporting false
  let some output ← IO.getEnv "INDEPENDENT_AUDIT_OUTPUT"
    | throwError "INDEPENDENT_AUDIT_OUTPUT required"
  let owned := (env.constants.fold (init := #[]) fun acc n ci =>
    if ownedModules.contains (moduleOf env n) then acc.push (n, ci) else acc).qsort
      (fun a b => Name.lt a.1 b.1)
  unless owned.size > 0 do throwError "NO_OWNED_DECLARATIONS"
  for m in ownedModules do
    unless env.header.moduleNames.any (fun n => n.toString == m) do
      throwError "OWNED_MODULE_NOT_IMPORTED {m}"
  let mut inventory : Array Json := #[]
  let mut violations : Array String := #[]
  for (n, ci) in owned do
    let axs ← collectAxioms n
    let pp ← liftTermElabM do
      return (← Meta.ppExpr ci.type).pretty
    inventory := inventory.push (Json.mkObj [
      ("declaration", nodeJson env n ci), ("type", toJson pp),
      ("axioms", toJson (axs.map Name.toString))])
    if ci.isAxiom then violations := violations.push s!"OWNED_AXIOM {n}"
    if ci.isUnsafe || ci.isPartial then violations := violations.push s!"UNSAFE_OR_PARTIAL_OWNED {n}"
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        violations := violations.push s!"UNEXPECTED_AXIOM {ax} IN {n}"
  IO.FS.writeFile (output ++ "/owned-inventory.json") (Json.arr inventory |>.pretty)
  IO.FS.writeFile (output ++ "/violations.json") (toJson violations |>.pretty)
  unless violations.isEmpty do throwError "OWNED_AUDIT_FAILED: {violations}"
  for r in requestedRoots do
    let some ci := env.find? r | throwError "REQUESTED_ROOT_MISSING {r}"
    unless ci.isTheorem && owned.any (fun (n, _) => n == r) do
      throwError "ROOT_NOT_OWNED_THEOREM {r}"
  let allClosure ← gather env (owned.toList.map Prod.fst) {}
  let rootClosure ← gather env requestedRoots.toList {}
  let mut graph : Array Json := #[]
  for (n, ci) in allClosure.toList.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    if ci.isUnsafe || ci.isPartial then throwError "UNSAFE_OR_PARTIAL_CLOSURE {n}"
    if ci.isAxiom then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "UNEXPECTED_CLOSURE_AXIOM {n}"
    graph := graph.push (nodeJson env n ci)
  IO.FS.writeFile (output ++ "/all-owned-closure.json") (Json.arr graph |>.compress)
  IO.FS.writeFile (output ++ "/requested-root-closure.json")
    (toJson ((rootClosure.toList.map Prod.fst).toArray.qsort Name.lt |>.map Name.toString) |>.pretty)
  let mut rootSummaries : Array Json := #[]
  for r in requestedRoots do
    let cs ← gather env [r] {}
    rootSummaries := rootSummaries.push <| Json.mkObj [
      ("name", toJson r.toString), ("closure_count", toJson cs.size)]
  logInfo m!"REPLAY_BEGIN all_owned={owned.size} closure={allClosure.size}; empty kernel trust=0"
  let base ← mkEmptyEnvironment 0
  unless base.constants.fold (init := 0) (fun k _ _ => k+1) == 0 do
    throwError "BASE_NOT_EMPTY"
  let verified ← base.toKernelEnv.replay allClosure
  for (n, original) in allClosure.toList do
    let some checked := verified.find? n | throwError "REPLAY_MISSING {n}"
    unless original.type == checked.type && original.levelParams == checked.levelParams do
      throwError "REPLAY_TYPE_OR_LEVEL_MISMATCH {n}"
  let summary := Json.mkObj [
    ("status", toJson "PASS"), ("trust_level", toJson (0 : Nat)),
    ("empty_base", toJson true), ("owned_count", toJson owned.size),
    ("all_owned_closure_count", toJson allClosure.size),
    ("requested_root_union_count", toJson rootClosure.size),
    ("roots", Json.arr rootSummaries)]
  IO.FS.writeFile (output ++ "/replay-summary.json") summary.pretty
  logInfo m!"ALL_OWNED_EMPTY_KERNEL_REPLAY_PASS {allClosure.size}"

end IndependentAudit
