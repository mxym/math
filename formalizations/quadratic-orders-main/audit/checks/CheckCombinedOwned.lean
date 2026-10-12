import ArithmeticSupplyWeakMain
import ArithmeticSupplyWeakMainReduction
import Entry002
import EmptyKernelReplay
import StockAxiomSnapshot
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array Name := #[`Entry002, `Entry002.Algebra, `Entry002.ArithmeticConductorConjugation, `Entry002.ArithmeticCore, `Entry002.ArithmeticFinitePrimeExclusion, `Entry002.ArithmeticInterface, `Entry002.ArithmeticLocalCongruence, `Entry002.ArithmeticPrimeIdealCounting, `Entry002.ArithmeticPrimeIdealRemainder, `Entry002.ArithmeticPrincipalSupplyAssembly, `Entry002.ArithmeticSplittingAsymptotics, `Entry002.ArithmeticSplittingCount, `Entry002.ArithmeticSplittingTower, `Entry002.ArithmeticSupplyElementary, `Entry002.ArithmeticWeakPrincipalSupplyAssembly, `Entry002.Assembly, `Entry002.BooleanCube, `Entry002.CRT, `Entry002.ComplexIsolation, `Entry002.Embedding, `Entry002.ExceptionalGraphs, `Entry002.FiniteLaw, `Entry002.FiniteProbability, `Entry002.FiniteSieveConsequences, `Entry002.GenericBackwardBatchCharge, `Entry002.GenericBackwardKernelCoverage, `Entry002.GenericBandParameters, `Entry002.GenericBatchSelection, `Entry002.GenericCommonWindowCharge, `Entry002.GenericCommonWindowNumerics, `Entry002.GenericCoverage, `Entry002.GenericCumulativeDyadicDensity, `Entry002.GenericDensityBands, `Entry002.GenericDyadicDensity, `Entry002.GenericFiniteSieveEngine, `Entry002.GenericFreshCoverage, `Entry002.GenericFreshEntropy, `Entry002.GenericGeometricBands, `Entry002.GenericGeometricEnrichment, `Entry002.GenericGeometricScale, `Entry002.GenericGrowthContradiction, `Entry002.GenericKernelCoverage, `Entry002.GenericMultiscaleEnrichment, `Entry002.GenericNumericalSchedule, `Entry002.GenericResidueGrowth, `Entry002.GenericResidues, `Entry002.GenericScaling, `Entry002.GenericSignSeparation, `Entry002.GenericSignedArithmetic, `Entry002.GenericStepEnrichment, `Entry002.GenericTimeKernels, `Entry002.GenericWalkExtraction, `Entry002.GenericWalkFrame, `Entry002.GenericWalkFreshEntropy, `Entry002.GenericWalkGeometry, `Entry002.GenericWalkPackage, `Entry002.GenericWalkPacking, `Entry002.GenericWalkTelescope, `Entry002.GenericWindowBandSizes, `Entry002.GenericWindowContradiction, `Entry002.GenericWindowEntropy, `Entry002.GenericWindowLogBudget, `Entry002.GenericWindowSchedule, `Entry002.GenericWindowTopEntropy, `Entry002.GenericWords, `Entry002.Graphs, `Entry002.IdealFactorLogarithm, `Entry002.IdealNormAnalytic, `Entry002.IdealNormCoefficient, `Entry002.IdealNormDivisibility, `Entry002.Information, `Entry002.Isolation, `Entry002.Minkowski, `Entry002.NormBound, `Entry002.OrderRestoration, `Entry002.Orders, `Entry002.PeriodicComponents, `Entry002.PosteriorCoverage, `Entry002.PrimeIdealAnalyticDefs, `Entry002.PrimeIdealChebyshev, `Entry002.PrimeIdealEulerLogAnalytic, `Entry002.PrimeIdealEulerLogIdentity, `Entry002.PrimeIdealEulerLogRealPole, `Entry002.PrimeIdealEulerLogRemainder, `Entry002.PrimeIdealLogConvolution, `Entry002.PrimeIdealLogDerivative, `Entry002.PrimeIdealNaturalPNTBridge, `Entry002.PrimeIdealPowerSummation, `Entry002.PrimeIdealSplitDirichlet, `Entry002.PrimeIdealSplitDirichletCutoff, `Entry002.PrimeIdealVonMangoldtBound, `Entry002.PrimeSupply, `Entry002.Restoration, `Entry002.RestorationInput, `Entry002.Sieve, `Entry002.SieveReduction, `Entry002.SignConcentration, `Entry002.Targets, `Entry002.Telescope, `Entry002.TinySteps, `Entry002.WeakAssembly, `Entry002.WeakCoreCommonWindowCharge, `Entry002.WeakCoreFiniteSieveSupport, `Entry002.WeakCoreFreshEntropy, `Entry002.WeakCoreGeometricBands, `Entry002.WeakCoreGeometricEnrichment, `Entry002.WeakCoreGeometricScale, `Entry002.WeakCoreGoodBinFiniteSieve, `Entry002.WeakCoreGoodBinWindowMass, `Entry002.WeakCoreSignSeparation, `Entry002.WeakCoreSignedArithmetic, `Entry002.WeakCoreWalkFreshEntropy, `Entry002.WeakCoreWeakTargets, `Entry002.WeakCoreWindowEntropy, `Entry002.WeakCoreWindowRates, `Entry002.WeakCoreWindowTopEntropy, `Entry002.WeakFiniteSieveConsequences, `Entry002.WeakPrincipalSupply, `Entry002.WeakSieveTargets, `Entry002.WeakSupplyDirichletCutoff, `Entry002.WeakSupplyDirichletGoodBins, `Entry002.WeakSupplyDyadicChebyshev, `Entry002.WeakSupplyDyadicSeries, `Entry002.WeakSupplyElementaryDiscount, `Entry002.WeakSupplyGoodBinUpper, `Entry002.WeakSupplyInterfaces, `Entry002.WeakSupplyWindowAveraging, `Entry002.WeakSupplyWindowIndependentGrid, `Entry002.WeakSupplyWindowLogCertificate, `ArithmeticSupplyRayBridge, `ArithmeticSupplyRayConductor, `ArithmeticSupplyWeakFromDirichlet, `ArithmeticSupplyWeakMainReduction, `ArithmeticSupplyWeakMain]
  for n in modules do
    unless env.header.moduleNames.contains n do throwError "Missing owned module {n}"
  let decls := env.constants.toList.filter fun (n, _) => IndependentAudit.belongs env modules n
  let mut rows : Array Json := #[]
  for (n, ci) in decls do
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("module", toJson ((IndependentAudit.moduleName? env n).map Name.toString)),
      ("kind", toJson (IndependentAudit.kind ci)),
      ("safe_root", toJson (IndependentAudit.safeLogicalRoot ci)),
      ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial)]
  let nonlogical := decls.filter fun (_, ci) => ci.isUnsafe || ci.isPartial
  let logicalNames := (decls.filter fun (_, ci) => !ci.isUnsafe && !ci.isPartial).map Prod.fst
  let all ← liftIO <| IndependentEmptyReplay.saturate env logicalNames
  let mut axioms : Array Name := #[]
  for n in all.toArray do
    let some ci := env.find? n | throwError "Missing closure constant {n}"
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial constant {n}"
    if ci.isAxiom then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Nonstandard axiom {n}"
      axioms := axioms.push n
  let actual ← match IndependentStockAxiomSnapshot.snapshot env with
    | .ok value => pure value
    | .error e => throwError "{e}"
  let text ← liftIO <| IO.FS.readFile "stock-standard-axioms.json"
  let expected ← match Json.parse text with
    | .ok value => pure value
    | .error e => throwError "{e}"
  unless actual == expected do throwError "Standard axiom type differs from stock"
  let some ci := env.find? `Entry002.arithmeticSupply_mainTarget_proved |
    throwError "Main endpoint missing"
  unless ci.isTheorem && ci.type == mkConst `Entry002.MainTarget do
    throwError "Main is not the literal unparameterized theorem"
  let mut paths : Array Json := #[]
  for mod in env.header.moduleNames do
    let path ← liftIO <| Lean.findOLean mod
    paths := paths.push <| Json.mkObj [("module", toJson mod.toString), ("path", toJson path.toString)]
  let result := Json.mkObj [
    ("status", toJson ("PASS" : String)),
    ("owned_modules", toJson (modules.map Name.toString)),
    ("inventory", toJson rows),
    ("resolved_paths", toJson paths),
    ("full_owned_closure_count", toJson all.size),
    ("nonlogical_generated_roots", toJson (nonlogical.map fun (n, _) => n.toString)),
    ("axioms", IndependentAudit.namesJson axioms),
    ("stock_axiom_types_equal", toJson true),
    ("literal_no_premise_Main", toJson true)]
  liftIO <| IO.FS.writeFile "combined-owned-inventory.json" (result.pretty ++ "\n")
  liftIO <| IO.FS.writeFile "combined-owned-closure.json" ((IndependentAudit.namesJson all.toArray).pretty ++ "\n")
  liftIO <| IO.println s!"COMBINED_PASS inventory={rows.size} closure={all.size}"
