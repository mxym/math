import Lake
open Lake DSL
package cofactor_spectral_asymptotics_progress
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib CofactorSpectralProgress where
  srcDir := "src"
  roots := #[
    `BapatColorExpansion,
    `BapatColorTransport,
    `BapatMultiColor,
    `BapatMvFischer,
    `BapatPermanentFischer,
    `BapatMixedFischer,
    `CofactorDefinitions,
    `CofactorComplexFock,
    `CofactorGramPSD,
    `CofactorEuclideanGram,
    `CofactorMarkedCoefficientLower,
    `CofactorTensorArrays,
    `CofactorContractionSquare,
    `CofactorCrossCardinality,
    `CofactorCrossNormalForm,
    `CofactorWeightedAverage,
    `CofactorCrossPositive,
    `CofactorIndicator,
    `CofactorBinaryNorm,
    `CofactorTargets,
    `CofactorHarmonicBound,
    `CofactorSortCoordinates,
    `CofactorFiniteBinaryNorm,
    `CofactorSignedBinaryNorm,
    `CofactorComplexBinaryNorm,
    `CofactorScaledBinaryNorm,
    `CofactorRayleighUpper,
    `CofactorExtremaUpper,
    `CofactorEigenvalueUpper,
    `CofactorLogarithmicUpper,
    `CofactorFiniteEntropy,
    `CofactorUpperMain,
    `CofactorGeometricMean,
    `CofactorGeometricEntropy,
    `CofactorEntropyProduct,
    `CofactorSignOrthogonality,
    `CofactorSignSquareAverage,
    `CofactorGroupedSignAverage
  ]
