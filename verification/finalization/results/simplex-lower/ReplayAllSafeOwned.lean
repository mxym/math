import Entry005.TruncationFormalization
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
  let modules : Array String := #["Entry005", "Entry005.ActualAssignmentAssembly", "Entry005.ActualBodyConeLaw", "Entry005.ActualBodyHorizontalMoment", "Entry005.ActualBodyJointConeInterface", "Entry005.ActualBodyPolarBoundary", "Entry005.ActualPyramidAssignment", "Entry005.ActualPyramidDefect", "Entry005.ActualPyramidJointCone", "Entry005.ActualPyramidMoment", "Entry005.AffineNormalization", "Entry005.AffinePyramid", "Entry005.AnchorCoordinates", "Entry005.AnchorSelection", "Entry005.AssignmentKernel", "Entry005.BallVolume", "Entry005.Cap", "Entry005.CentroidMaximumBound", "Entry005.ClippedAssignmentKernel", "Entry005.CompactBallConeLaw", "Entry005.CompactIidMomentContinuity", "Entry005.CompactProbabilitySubsequence", "Entry005.ConeLawFinite", "Entry005.ConeLawGeometry", "Entry005.Constants", "Entry005.CovarianceConditioning", "Entry005.DeterminantMoment", "Entry005.DeterminantWitness", "Entry005.EntryAffineInvariance", "Entry005.FacetRadialMass", "Entry005.FamilyWitness", "Entry005.FiniteBodyWeightedAssignment", "Entry005.FiniteDeterminantTupleInjection", "Entry005.FiniteHalfspaceCauchy", "Entry005.FiniteHalfspaceConeLaw", "Entry005.FiniteHalfspaceFacets", "Entry005.FiniteHalfspaceHorizontalMoment", "Entry005.FiniteLawZonotopeMoment", "Entry005.FirstMomentAssignment", "Entry005.GeometricEndpoint", "Entry005.HalfspaceApproximation", "Entry005.HalfspaceApproximationSequence", "Entry005.Handoff", "Entry005.HausdorffRetention", "Entry005.HyperplaneProjectionJacobian", "Entry005.IidAnchorAffineDeterminant", "Entry005.IidAnchorFirstMomentPositive", "Entry005.IidAnchorSpanningSupport", "Entry005.IidTransport", "Entry005.IidWeightedAnchorSelection", "Entry005.IntegratedWitness", "Entry005.IntrinsicLinearImageReuse", "Entry005.LargestCoordinate", "Entry005.MaximumOuterBall", "Entry005.OfficialProjectionDefinitions", "Entry005.PaperWitnessCombinatorics", "Entry005.PaperWitnessTransport", "Entry005.PrescribedSimplex", "Entry005.ProjectionAffineTransport", "Entry005.ProjectionBodyCovariance", "Entry005.ProjectionBodyDirections", "Entry005.ProjectionCap", "Entry005.ProjectionVolumeSqueeze", "Entry005.PyramidContinuity", "Entry005.PyramidEntryDefect", "Entry005.PyramidFacetAreas", "Entry005.PyramidFormalization", "Entry005.PyramidHalfspaces", "Entry005.PyramidIidMomentReuse", "Entry005.PyramidLiftCoordinates", "Entry005.PyramidLiftedMoment", "Entry005.PyramidMomentDefect", "Entry005.PyramidProjectionBody", "Entry005.PyramidProjectionVolume", "Entry005.PyramidSideArea", "Entry005.PyramidSideFrame", "Entry005.PyramidVolume", "Entry005.PyramidZonotopeAlgebra", "Entry005.RadialConeVolume", "Entry005.RadialPowerIntegral", "Entry005.RegularSimplex", "Entry005.RoundAnchorChain", "Entry005.SelectedAnchorSimplex", "Entry005.SharpNormalizationRadius", "Entry005.SimplexVolumeInterface", "Entry005.StrongBallVolume", "Entry005.StrongGeometricEndpoint", "Entry005.StrongProjectionCap", "Entry005.Targets", "Entry005.ThresholdGate", "Entry005.TruncationActualDefect", "Entry005.TruncationCenteredHalfspaces", "Entry005.TruncationCentroid", "Entry005.TruncationConvexDeterminant", "Entry005.TruncationCoordinateFacets", "Entry005.TruncationDefinitions", "Entry005.TruncationFacetDeterminants", "Entry005.TruncationFacetFormula", "Entry005.TruncationFacetGeometry", "Entry005.TruncationFacetTranslation", "Entry005.TruncationFacetVectors", "Entry005.TruncationFormalization", "Entry005.TruncationGeometry", "Entry005.TruncationMaximum", "Entry005.TruncationPower", "Entry005.TruncationProjection", "Entry005.TruncationRationalDefect", "Entry005.TruncationScalarCancellation", "Entry005.TruncationSharpness", "Entry005.TruncationSharpnessAssembly", "Entry005.TruncationSimplexActualVolume", "Entry005.TruncationSimplexVolume", "Entry005.TruncationVolume", "Entry005.UnitBallAnchorChain", "Entry005.UnitBallDeterminant", "Entry005.WeightedAnchorSelection", "Entry005.WitnessAnchorChain", "Entry005.ZonotopeDeterminant", "Entry005.ZonotopeFormula", "Entry005.ZonotopeInjectionCombinatorics", "Entry005.ZonotopeVolume", "Mxym.StochasticRigidity", "OAI.Geometry.ProjectionVolume.Basic", "OAI.Geometry.ProjectionVolume.Brightness", "OAI.Geometry.ProjectionVolume.Model"]
  let mut roots : Array Name := #[]
  let mut skipped : Array String := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if modules.contains env.header.moduleNames[idx.toNat]!.toString then
        if ci.isUnsafe || ci.isPartial then skipped := skipped.push n.toString
        else roots := roots.push n
  unless skipped.isEmpty do throwError "Unexpected unsafe/partial owned nodes {skipped}"
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
  let base ← mkEmptyEnvironment 0
  let verified ← base.toKernelEnv.replay cs
  for r in roots do
    let some original := env.find? r | throwError "Original root absent {r}"
    let some checked := verified.find? r | throwError "Replayed root absent {r}"
    unless original.type == checked.type && original.levelParams == checked.levelParams do
      throwError "Root type/levels changed {r}"
  logInfo m!"ALL_SAFE_OWNED_EMPTY_KERNEL_REPLAY_PASS roots={roots.size} closure={cs.size}"
