import BapatColorExpansion
import BapatColorTransport
import BapatMultiColor
import BapatMvFischer
import BapatPermanentFischer
import BapatMixedFischer
import CofactorDefinitions
import CofactorComplexFock
import CofactorGramPSD
import CofactorEuclideanGram
import CofactorMarkedCoefficientLower
import CofactorTensorArrays
import CofactorContractionSquare
import CofactorCrossCardinality
import CofactorPureCoefficient
import CofactorBinaryMarkedLower
import CofactorCrossNormalForm
import CofactorWeightedAverage
import CofactorCrossPositive
import CofactorIndicator
import CofactorBinaryNorm
import CofactorTargets
import CofactorHarmonicBound
import CofactorNormalizedRows
import CofactorSortCoordinates
import CofactorBinaryPermanent
import CofactorFiniteBinaryNorm
import CofactorNormalizedRankTwo
import CofactorCoefficientRatio
import CofactorSignedBinaryNorm
import CofactorComplexBinaryNorm
import CofactorScaledBinaryNorm
import CofactorRayleighUpper
import CofactorExtremaUpper
import CofactorEigenvalueUpper
import CofactorLogarithmicUpper
import CofactorFiniteEntropy
import CofactorUpperMain
import CofactorGeometricMean
import CofactorGeometricEntropy
import CofactorEntropyProduct
import CofactorRootRingProduct
import CofactorSignOrthogonality
import CofactorRootRingMoments
import CofactorSignSquareAverage
import CofactorBinaryRayleighLower
import CofactorGroupedSignAverage
import CofactorSignedRootRing
import CofactorRingFamily
import CofactorRingPolynomial
import CofactorSignedRingCoefficients
import CofactorRingSignChoice
import CofactorFiniteRingConstruction
import CofactorRingConstructionFin
import Lean
import Lean.Replay

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


open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.all true

namespace IndependentAudit

def ownedModules : Array String := #[ "BapatColorExpansion", "BapatColorTransport", "BapatMultiColor", "BapatMvFischer", "BapatPermanentFischer", "BapatMixedFischer", "CofactorDefinitions", "CofactorComplexFock", "CofactorGramPSD", "CofactorEuclideanGram", "CofactorMarkedCoefficientLower", "CofactorTensorArrays", "CofactorContractionSquare", "CofactorCrossCardinality", "CofactorPureCoefficient", "CofactorBinaryMarkedLower", "CofactorCrossNormalForm", "CofactorWeightedAverage", "CofactorCrossPositive", "CofactorIndicator", "CofactorBinaryNorm", "CofactorTargets", "CofactorHarmonicBound", "CofactorNormalizedRows", "CofactorSortCoordinates", "CofactorBinaryPermanent", "CofactorFiniteBinaryNorm", "CofactorNormalizedRankTwo", "CofactorCoefficientRatio", "CofactorSignedBinaryNorm", "CofactorComplexBinaryNorm", "CofactorScaledBinaryNorm", "CofactorRayleighUpper", "CofactorExtremaUpper", "CofactorEigenvalueUpper", "CofactorLogarithmicUpper", "CofactorFiniteEntropy", "CofactorUpperMain", "CofactorGeometricMean", "CofactorGeometricEntropy", "CofactorEntropyProduct", "CofactorRootRingProduct", "CofactorSignOrthogonality", "CofactorRootRingMoments", "CofactorSignSquareAverage", "CofactorBinaryRayleighLower", "CofactorGroupedSignAverage", "CofactorSignedRootRing", "CofactorRingFamily", "CofactorRingPolynomial", "CofactorSignedRingCoefficients", "CofactorRingSignChoice", "CofactorFiniteRingConstruction", "CofactorRingConstructionFin" ]
def requestedRoots : Array Name := #[ ``CofactorSpectral.compound_indicator_sum, ``CofactorSpectral.compound_psd, ``CofactorSpectral.firstCofactor_eq_deletedMinor, ``CofactorSpectral.complex_binary_norm_bound, ``CofactorSpectral.real_binary_norm_bound, ``CofactorSpectral.compound_largest_eigenvalue_upper, ``CofactorSpectral.realCompound_largest_eigenvalue_upper, ``CofactorSpectral.complexExtremum_upper, ``CofactorSpectral.realExtremum_upper, ``CofactorSpectral.complexExtremum_eventual_log_upper, ``CofactorSpectral.realExtremum_eventual_log_upper, ``CofactorSpectral.rankTwoComplexExtremum_eventual_log_upper, ``CofactorSpectral.rankTwoRealExtremum_eventual_log_upper, ``CofactorSpectral.pdComplexExtremum_eventual_log_upper, ``CofactorSpectral.pdRealExtremum_eventual_log_upper, ``CofactorSpectral.finite_gibbs_inequality, ``CofactorSpectral.geometrically_separated_mean_bound, ``CofactorSpectral.geometric_separation_product_bound, ``CofactorSpectral.signCharacter_orthogonality, ``CofactorSpectral.groupedSignCombination_square_average, ``CofactorSpectral.groupedSignCombination_has_small_choice, ``CofactorSpectral.marked_coefficient_quadratic_lower, ``CofactorSpectral.exists_signed_root_ring, ``CofactorSpectral.normalizedBinaryGram_rankTwoCorrelationAdmissible, ``CofactorSpectral.normalizedBinaryGram_complex_test_lower, ``CofactorSpectral.normalizedBinaryGram_real_test_lower, ``CofactorSpectral.normalizedBinaryGram_permanent_ratio, ``CofactorSpectral.signedRingPolynomial_has_small_choice, ``CofactorSpectral.exists_rankTwoCorrelation_ring_bound ]

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
  match StandardAxiomGuard.validateEnvironment env with
  | .error e => throwError "{e}"
  | .ok _ => pure ()
  let some output ← IO.getEnv "INDEPENDENT_AUDIT_OUTPUT"
    | throwError "INDEPENDENT_AUDIT_OUTPUT required"
  IO.FS.writeFile (output ++ "/standard-axioms.json") (← StandardAxiomGuard.exportJson env).pretty
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
