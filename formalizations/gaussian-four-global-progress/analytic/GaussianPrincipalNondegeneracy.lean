import GaussianCenteredRowIndependence
import GaussianMinimalCovarianceRows
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! A positive-definite principal covariance block makes the actual minimal
Gaussian score realization an affinely independent simplex. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {n : ℕ} [NeZero n]

theorem covarianceRows_linearIndependent
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    LinearIndependent ℝ (covarianceRows A) := by
  apply Matrix.linearIndependent_of_posDef_gram
  change (scoreGram (covarianceRows A)).PosDef
  rw [scoreGram_covarianceRows A hA.posSemidef]
  exact hA

theorem minimalCovarianceRows_affineIndependent
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hQ : (principalCovariance Q).PosDef) :
    AffineIndependent ℝ (minimalCovarianceRows Q) := by
  change AffineIndependent ℝ (centeredRowFamily (covarianceRows (principalCovariance Q)))
  exact centeredRowFamily_affineIndependent _ (covarianceRows_linearIndependent _ hQ)

end GaussianMeasureBridge
