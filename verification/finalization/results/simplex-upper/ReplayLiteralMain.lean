import Entry005
import Entry005.ActualAssignmentAssembly
import Entry005.ActualBodyConeLaw
import Entry005.ActualBodyHorizontalMoment
import Entry005.ActualBodyJointConeInterface
import Entry005.ActualBodyPolarBoundary
import Entry005.ActualFiniteEnclosingCap
import Entry005.ActualFiniteEnclosingRadialCap
import Entry005.ActualNormalizedDirectionalRoundness
import Entry005.ActualPyramidAssignment
import Entry005.ActualPyramidDefect
import Entry005.ActualPyramidJointCone
import Entry005.ActualPyramidMoment
import Entry005.ActualSupportFirstVariationTest
import Entry005.AffineNormalization
import Entry005.AffinePyramid
import Entry005.AnchorCoordinates
import Entry005.AnchorSelection
import Entry005.AssignmentKernel
import Entry005.BallVolume
import Entry005.Cap
import Entry005.CenteredAtomCorrection
import Entry005.CentroidMaximumBound
import Entry005.ClippedAssignmentKernel
import Entry005.CompactBallConeLaw
import Entry005.CompactIidMomentContinuity
import Entry005.CompactProbabilitySubsequence
import Entry005.ConditionalPyramidMomentBridge
import Entry005.ConeLawFinite
import Entry005.ConeLawGeometry
import Entry005.Constants
import Entry005.CovarianceConditioning
import Entry005.DeterminantMoment
import Entry005.DeterminantWitness
import Entry005.EntryAffineInvariance
import Entry005.FacetRadialMass
import Entry005.FamilyWitness
import Entry005.FiniteBodyWeightedAssignment
import Entry005.FiniteDeterminantTupleInjection
import Entry005.FiniteHalfspaceCauchy
import Entry005.FiniteHalfspaceCenteredCorrection
import Entry005.FiniteHalfspaceConeLaw
import Entry005.FiniteHalfspaceFacets
import Entry005.FiniteHalfspaceHorizontalMoment
import Entry005.FiniteLawZonotopeMoment
import Entry005.FiniteMinkowskiScaleGate
import Entry005.FiniteRadialSupportScale
import Entry005.FirstMomentAssignment
import Entry005.GeometricEndpoint
import Entry005.HalfspaceApproximation
import Entry005.HalfspaceApproximationSequence
import Entry005.Handoff
import Entry005.HausdorffRetention
import Entry005.HyperplaneProjectionJacobian
import Entry005.IidAnchorAffineDeterminant
import Entry005.IidAnchorFirstMomentPositive
import Entry005.IidAnchorSpanningSupport
import Entry005.IidTransport
import Entry005.IidWeightedAnchorSelection
import Entry005.IntegratedWitness
import Entry005.IntrinsicLinearImageReuse
import Entry005.LargestCoordinate
import Entry005.MainTarget
import Entry005.MaximumOuterBall
import Entry005.OfficialProjectionDefinitions
import Entry005.OriginalRadialScale
import Entry005.PaperWitnessCombinatorics
import Entry005.PaperWitnessTransport
import Entry005.PolarSimplexConstruction
import Entry005.PrescribedSimplex
import Entry005.ProjectionAffineTransport
import Entry005.ProjectionBodyCovariance
import Entry005.ProjectionBodyDirections
import Entry005.ProjectionCap
import Entry005.ProjectionScaleAssembly
import Entry005.ProjectionVolumeSqueeze
import Entry005.PyramidApproximationLimits
import Entry005.PyramidContinuity
import Entry005.PyramidEntryDefect
import Entry005.PyramidFacetAreas
import Entry005.PyramidFormalization
import Entry005.PyramidHalfspaces
import Entry005.PyramidIidMomentReuse
import Entry005.PyramidLiftCoordinates
import Entry005.PyramidLiftedMoment
import Entry005.PyramidMomentDefect
import Entry005.PyramidProjectionBody
import Entry005.PyramidProjectionVolume
import Entry005.PyramidSideArea
import Entry005.PyramidSideFrame
import Entry005.PyramidVolume
import Entry005.PyramidZonotopeAlgebra
import Entry005.RadialConeVolume
import Entry005.RadialPowerIntegral
import Entry005.RegularSimplex
import Entry005.RoundAnchorChain
import Entry005.SameWitnessOriginalQBudget
import Entry005.SelectedAnchorHullRoundness
import Entry005.SelectedAnchorSimplex
import Entry005.SharpConstantGates
import Entry005.SharpMainRetentionAssembly
import Entry005.SharpNormalizationRadius
import Entry005.SharpUpperMain
import Entry005.SimplexVolumeInterface
import Entry005.StrongBallVolume
import Entry005.StrongGeometricEndpoint
import Entry005.StrongProjectionCap
import Entry005.SupportScaleCapAssembly
import Entry005.Targets
import Entry005.ThresholdGate
import Entry005.UnitBallAnchorChain
import Entry005.UnitBallDeterminant
import Entry005.VerifiedPyramidMomentBridge
import Entry005.WeightedAnchorSelection
import Entry005.WitnessAnchorChain
import Entry005.ZonotopeDeterminant
import Entry005.ZonotopeFormula
import Entry005.ZonotopeInjectionCombinatorics
import Entry005.ZonotopeVolume
import Mxym.StochasticRigidity
import OAI.Geometry.ProjectionVolume.Basic
import OAI.Geometry.ProjectionVolume.Brightness
import OAI.Geometry.ProjectionVolume.Model
import Lean.Replay
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
partial def gather (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : Except String (Std.HashMap Name ConstantInfo) :=
  match todo with
  | [] => .ok seen
  | n :: todo =>
    if seen.contains n then gather env todo seen
    else match env.find? n with
    | none => .error s!"Missing referenced declaration {n}"
    | some ci =>
      let extra := match ci with
        | .inductInfo v => v.all ++ v.ctors
        | .ctorInfo v => [v.induct]
        | .recInfo v => v.all
        | _ => []
      gather env (extra ++ ci.getUsedConstantsAsSet.toList ++ todo) (seen.insert n ci)
run_cmd do
  let env := (← getEnv).setExporting false
  let modulesForMain : Array String := #["Entry005", "Entry005.ActualAssignmentAssembly", "Entry005.ActualBodyConeLaw", "Entry005.ActualBodyHorizontalMoment", "Entry005.ActualBodyJointConeInterface", "Entry005.ActualBodyPolarBoundary", "Entry005.ActualFiniteEnclosingCap", "Entry005.ActualFiniteEnclosingRadialCap", "Entry005.ActualNormalizedDirectionalRoundness", "Entry005.ActualPyramidAssignment", "Entry005.ActualPyramidDefect", "Entry005.ActualPyramidJointCone", "Entry005.ActualPyramidMoment", "Entry005.ActualSupportFirstVariationTest", "Entry005.AffineNormalization", "Entry005.AffinePyramid", "Entry005.AnchorCoordinates", "Entry005.AnchorSelection", "Entry005.AssignmentKernel", "Entry005.BallVolume", "Entry005.Cap", "Entry005.CenteredAtomCorrection", "Entry005.CentroidMaximumBound", "Entry005.ClippedAssignmentKernel", "Entry005.CompactBallConeLaw", "Entry005.CompactIidMomentContinuity", "Entry005.CompactProbabilitySubsequence", "Entry005.ConditionalPyramidMomentBridge", "Entry005.ConeLawFinite", "Entry005.ConeLawGeometry", "Entry005.Constants", "Entry005.CovarianceConditioning", "Entry005.DeterminantMoment", "Entry005.DeterminantWitness", "Entry005.EntryAffineInvariance", "Entry005.FacetRadialMass", "Entry005.FamilyWitness", "Entry005.FiniteBodyWeightedAssignment", "Entry005.FiniteDeterminantTupleInjection", "Entry005.FiniteHalfspaceCauchy", "Entry005.FiniteHalfspaceCenteredCorrection", "Entry005.FiniteHalfspaceConeLaw", "Entry005.FiniteHalfspaceFacets", "Entry005.FiniteHalfspaceHorizontalMoment", "Entry005.FiniteLawZonotopeMoment", "Entry005.FiniteMinkowskiScaleGate", "Entry005.FiniteRadialSupportScale", "Entry005.FirstMomentAssignment", "Entry005.GeometricEndpoint", "Entry005.HalfspaceApproximation", "Entry005.HalfspaceApproximationSequence", "Entry005.Handoff", "Entry005.HausdorffRetention", "Entry005.HyperplaneProjectionJacobian", "Entry005.IidAnchorAffineDeterminant", "Entry005.IidAnchorFirstMomentPositive", "Entry005.IidAnchorSpanningSupport", "Entry005.IidTransport", "Entry005.IidWeightedAnchorSelection", "Entry005.IntegratedWitness", "Entry005.IntrinsicLinearImageReuse", "Entry005.LargestCoordinate", "Entry005.MainTarget", "Entry005.MaximumOuterBall", "Entry005.OfficialProjectionDefinitions", "Entry005.OriginalRadialScale", "Entry005.PaperWitnessCombinatorics", "Entry005.PaperWitnessTransport", "Entry005.PolarSimplexConstruction", "Entry005.PrescribedSimplex", "Entry005.ProjectionAffineTransport", "Entry005.ProjectionBodyCovariance", "Entry005.ProjectionBodyDirections", "Entry005.ProjectionCap", "Entry005.ProjectionScaleAssembly", "Entry005.ProjectionVolumeSqueeze", "Entry005.PyramidApproximationLimits", "Entry005.PyramidContinuity", "Entry005.PyramidEntryDefect", "Entry005.PyramidFacetAreas", "Entry005.PyramidFormalization", "Entry005.PyramidHalfspaces", "Entry005.PyramidIidMomentReuse", "Entry005.PyramidLiftCoordinates", "Entry005.PyramidLiftedMoment", "Entry005.PyramidMomentDefect", "Entry005.PyramidProjectionBody", "Entry005.PyramidProjectionVolume", "Entry005.PyramidSideArea", "Entry005.PyramidSideFrame", "Entry005.PyramidVolume", "Entry005.PyramidZonotopeAlgebra", "Entry005.RadialConeVolume", "Entry005.RadialPowerIntegral", "Entry005.RegularSimplex", "Entry005.RoundAnchorChain", "Entry005.SameWitnessOriginalQBudget", "Entry005.SelectedAnchorHullRoundness", "Entry005.SelectedAnchorSimplex", "Entry005.SharpConstantGates", "Entry005.SharpMainRetentionAssembly", "Entry005.SharpNormalizationRadius", "Entry005.SharpUpperMain", "Entry005.SimplexVolumeInterface", "Entry005.StrongBallVolume", "Entry005.StrongGeometricEndpoint", "Entry005.StrongProjectionCap", "Entry005.SupportScaleCapAssembly", "Entry005.Targets", "Entry005.ThresholdGate", "Entry005.UnitBallAnchorChain", "Entry005.UnitBallDeterminant", "Entry005.VerifiedPyramidMomentBridge", "Entry005.WeightedAnchorSelection", "Entry005.WitnessAnchorChain", "Entry005.ZonotopeDeterminant", "Entry005.ZonotopeFormula", "Entry005.ZonotopeInjectionCombinatorics", "Entry005.ZonotopeVolume", "Mxym.StochasticRigidity", "OAI.Geometry.ProjectionVolume.Basic", "OAI.Geometry.ProjectionVolume.Brightness", "OAI.Geometry.ProjectionVolume.Model"]
  let roots : Array Name := #[``Entry005.sharpMain]
  let skipped : Array String := #[]
  let cs ← match gather env roots.toList {} with
    | .ok cs => pure cs
    | .error err => throwError "{err}"
  for (n, ci) in cs.toList do
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial replay node {n}"
    if ci.isAxiom then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected replay axiom {n}"

  let mut graphRows : Array Json := #[]
  for (n, ci) in cs.toList do
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "(kernel)"
    let extra := match ci with
      | .inductInfo v => v.all ++ v.ctors
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | _ => []
    graphRows := graphRows.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson moduleName),
      ("all_direct", toJson ((extra ++ ci.getUsedConstantsAsSet.toList).map Name.toString)),
      ("axiom", toJson ci.isAxiom), ("unsafe", toJson ci.isUnsafe),
      ("partial", toJson ci.isPartial)]
  let some graphPath ← IO.getEnv "FINALIZATION_GRAPH_PATH" |
    throwError "Missing graph output path"
  liftIO <| IO.FS.writeFile graphPath (Json.compress (toJson graphRows))
  logInfo m!"REPLAY_BEGIN roots={roots.size} closure={cs.size} skipped={Json.compress (toJson skipped)} trust=0 empty=true"
  for r in roots do
    let some ci := env.find? r | throwError "Missing main root"
    unless ci.isTheorem do throwError "Main is not a theorem"
  let mut own : Array String := #[]
  for (n, _) in cs.toList do
    if let some idx := env.getModuleIdxFor? n then
      if modulesForMain.contains env.header.moduleNames[idx.toNat]!.toString then
        own := own.push n.toString
  logInfo s!"MAIN_OWNED_CLOSURE_JSON={Json.compress (toJson own)}"
  let base ← mkEmptyEnvironment 0
  let verified ← base.toKernelEnv.replay cs
  for r in roots do
    let some original := env.find? r | throwError "Original root absent {r}"
    let some checked := verified.find? r | throwError "Replayed root absent {r}"
    unless original.type == checked.type && original.levelParams == checked.levelParams do
      throwError "Root type/levels changed {r}"
  logInfo m!"MAIN_EMPTY_KERNEL_REPLAY_PASS roots={roots.size} closure={cs.size}"
