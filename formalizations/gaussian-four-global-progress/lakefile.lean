import Lake
open Lake DSL

package gaussianFourGlobalProgress

require gaussianMeasureBridge from "../gaussian-measure-primal-dual"

lean_lib GaussianFourProfileSupport where
  srcDir := "../gaussian-mass-envelope-progress"
  roots := #[`GaussianHalflineFlux, `GaussianHalfspaceFlux, `GaussianTail,
    `GaussianHazard, `GaussianQuantile, `GaussianOneCell]

lean_lib GaussianFourAnalyticSupport where
  srcDir := "analytic"
  roots := #[
    `GaussianCoordinateSplit,
    `GaussianBalancedValue,
    `GaussianScoreDerivative,
    `GaussianValueScaling,
    `GaussianCovarianceValue,
    `GaussianScoreSymmetry,
    `GaussianRotationalMomentIdentity,
    `GaussianSliceFlux,
    `GaussianPolyhedralGraphFlux,
    `GaussianGraphLift,
    `GaussianMaskedSliceFlux,
    `GaussianGraphVectorFlux,
    `GaussianPriceContinuity,
    `GaussianWinningContinuity,
    `GaussianCovarianceContinuity,
    `GaussianMomentCovariance,
    `GaussianRegularValue,
    `GaussianMomentSymmetry,
    `GaussianWinningGraphFlux,
    `GaussianNormalCoordinates,
    `GaussianFacetDensityPositive,
    `GaussianSimplicialFlux,
    `GaussianAllCellsFlux,
    `GaussianCenteredRowIndependence,
    `GaussianMinimalCovarianceRows,
    `GaussianPrincipalNondegeneracy,
    `GaussianAffineMatrixFactorization,
    `GaussianActualEnvelope,
    `GaussianDiagonalCovarianceDerivative,
    `GaussianPositiveAffineLift,
    `GaussianCenteredCovarianceBlock,
    `GaussianCenteredAffineLift,
    `GaussianFluxCoefficientSymmetry,
    `GaussianSymmetricFlux,
    `GaussianSimplexAlgebra,
    `GaussianFluxEnergy,
    `GaussianCovarianceFluxDerivative,
    `GaussianFacetLaplacian,
    `GaussianAffineLiftDerivative,
    `GaussianCovarianceDifferential,
    `GaussianGramIsometry,
    `GaussianWinningMomentSpan,
    `GaussianGramMomentTransport,
    `GaussianTailCalculus,
    `GaussianGraphMassDerivative,
    `GaussianWinningMassDerivative,
    `GaussianSimplicialMassFlux]

@[default_target]
lean_lib GaussianFour where
  roots := #[`GaussianFour]
