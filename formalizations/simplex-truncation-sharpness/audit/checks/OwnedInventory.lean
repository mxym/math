import Entry005.TruncationFormalization
import Lean.Replay
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option pp.universes true
set_option format.width 160
run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array String := #["Entry005", "Entry005.ActualAssignmentAssembly", "Entry005.ActualBodyConeLaw", "Entry005.ActualBodyHorizontalMoment", "Entry005.ActualBodyJointConeInterface", "Entry005.ActualBodyPolarBoundary", "Entry005.ActualPyramidAssignment", "Entry005.ActualPyramidDefect", "Entry005.ActualPyramidJointCone", "Entry005.ActualPyramidMoment", "Entry005.AffineNormalization", "Entry005.AffinePyramid", "Entry005.AnchorCoordinates", "Entry005.AnchorSelection", "Entry005.AssignmentKernel", "Entry005.BallVolume", "Entry005.Cap", "Entry005.CentroidMaximumBound", "Entry005.ClippedAssignmentKernel", "Entry005.CompactBallConeLaw", "Entry005.CompactIidMomentContinuity", "Entry005.CompactProbabilitySubsequence", "Entry005.ConeLawFinite", "Entry005.ConeLawGeometry", "Entry005.Constants", "Entry005.CovarianceConditioning", "Entry005.DeterminantMoment", "Entry005.DeterminantWitness", "Entry005.EntryAffineInvariance", "Entry005.FacetRadialMass", "Entry005.FamilyWitness", "Entry005.FiniteBodyWeightedAssignment", "Entry005.FiniteDeterminantTupleInjection", "Entry005.FiniteHalfspaceCauchy", "Entry005.FiniteHalfspaceConeLaw", "Entry005.FiniteHalfspaceFacets", "Entry005.FiniteHalfspaceHorizontalMoment", "Entry005.FiniteLawZonotopeMoment", "Entry005.FirstMomentAssignment", "Entry005.GeometricEndpoint", "Entry005.HalfspaceApproximation", "Entry005.HalfspaceApproximationSequence", "Entry005.Handoff", "Entry005.HausdorffRetention", "Entry005.HyperplaneProjectionJacobian", "Entry005.IidAnchorAffineDeterminant", "Entry005.IidAnchorFirstMomentPositive", "Entry005.IidAnchorSpanningSupport", "Entry005.IidTransport", "Entry005.IidWeightedAnchorSelection", "Entry005.IntegratedWitness", "Entry005.IntrinsicLinearImageReuse", "Entry005.LargestCoordinate", "Entry005.MaximumOuterBall", "Entry005.OfficialProjectionDefinitions", "Entry005.PaperWitnessCombinatorics", "Entry005.PaperWitnessTransport", "Entry005.PrescribedSimplex", "Entry005.ProjectionAffineTransport", "Entry005.ProjectionBodyCovariance", "Entry005.ProjectionBodyDirections", "Entry005.ProjectionCap", "Entry005.ProjectionVolumeSqueeze", "Entry005.PyramidContinuity", "Entry005.PyramidEntryDefect", "Entry005.PyramidFacetAreas", "Entry005.PyramidFormalization", "Entry005.PyramidHalfspaces", "Entry005.PyramidIidMomentReuse", "Entry005.PyramidLiftCoordinates", "Entry005.PyramidLiftedMoment", "Entry005.PyramidMomentDefect", "Entry005.PyramidProjectionBody", "Entry005.PyramidProjectionVolume", "Entry005.PyramidSideArea", "Entry005.PyramidSideFrame", "Entry005.PyramidVolume", "Entry005.PyramidZonotopeAlgebra", "Entry005.RadialConeVolume", "Entry005.RadialPowerIntegral", "Entry005.RegularSimplex", "Entry005.RoundAnchorChain", "Entry005.SelectedAnchorSimplex", "Entry005.SharpNormalizationRadius", "Entry005.SimplexVolumeInterface", "Entry005.StrongBallVolume", "Entry005.StrongGeometricEndpoint", "Entry005.StrongProjectionCap", "Entry005.Targets", "Entry005.ThresholdGate", "Entry005.TruncationActualDefect", "Entry005.TruncationCenteredHalfspaces", "Entry005.TruncationCentroid", "Entry005.TruncationConvexDeterminant", "Entry005.TruncationCoordinateFacets", "Entry005.TruncationDefinitions", "Entry005.TruncationFacetDeterminants", "Entry005.TruncationFacetFormula", "Entry005.TruncationFacetGeometry", "Entry005.TruncationFacetTranslation", "Entry005.TruncationFacetVectors", "Entry005.TruncationFormalization", "Entry005.TruncationGeometry", "Entry005.TruncationMaximum", "Entry005.TruncationPower", "Entry005.TruncationProjection", "Entry005.TruncationRationalDefect", "Entry005.TruncationScalarCancellation", "Entry005.TruncationSharpness", "Entry005.TruncationSharpnessAssembly", "Entry005.TruncationSimplexActualVolume", "Entry005.TruncationSimplexVolume", "Entry005.TruncationVolume", "Entry005.UnitBallAnchorChain", "Entry005.UnitBallDeterminant", "Entry005.WeightedAnchorSelection", "Entry005.WitnessAnchorChain", "Entry005.ZonotopeDeterminant", "Entry005.ZonotopeFormula", "Entry005.ZonotopeInjectionCombinatorics", "Entry005.ZonotopeVolume", "Mxym.StochasticRigidity", "OAI.Geometry.ProjectionVolume.Basic", "OAI.Geometry.ProjectionVolume.Brightness", "OAI.Geometry.ProjectionVolume.Model"]
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let modName := env.header.moduleNames[idx.toNat]!
      if modules.contains modName.toString then
        let typ ← liftTermElabM <| Meta.ppExpr ci.type
        let ax ← collectAxioms n
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let un := privateToUserName n
        let namespaceSelected := (`Entry005).isPrefixOf un || (`Mxym).isPrefixOf un || (`OAI).isPrefixOf un
        rows := rows.push <| Json.mkObj [("name",toJson n.toString),
          ("module",toJson modName.toString),("type",toJson typ.pretty),
          ("kind",toJson kind),("unsafe",toJson ci.isUnsafe),("partial",toJson ci.isPartial),
          ("namespace_selected",toJson namespaceSelected),
          ("axioms",toJson ((ax.qsort Name.lt).map Name.toString))]
  logInfo s!"OWNED_INVENTORY_JSON={Json.compress (toJson rows)}"
