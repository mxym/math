import GaussianCovarianceValue
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace GaussianMeasureBridge

variable {k : ℕ} [NeZero k]

/-- Continuity of the canonical score rows on the closed PSD cone, including
its rank-deficient boundary. -/
theorem continuousOn_covarianceRows :
    ContinuousOn (covarianceRows (k := k)) {Q | Q.PosSemidef} := by
  have h : ContinuousOn (CFC.sqrt : Matrix (Fin k) (Fin k) ℝ → _)
      {Q | Q.PosSemidef} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using
      (CFC.continuousOn_sqrt : ContinuousOn (CFC.sqrt : Matrix (Fin k) (Fin k) ℝ → _)
        {Q | 0 ≤ Q})
  exact (show Continuous (fun B : Matrix (Fin k) (Fin k) ℝ =>
    fun i => WithLp.toLp 2 (B i)) by fun_prop).comp_continuousOn h

/-- The actual integral-defined covariance value is continuous all the way to
singular covariances. -/
theorem continuousOn_covarianceValue :
    ContinuousOn (covarianceValue (k := k)) {Q | Q.PosSemidef} := by
  have h := continuous_equalMassValue.comp_continuousOn
    (continuousOn_covarianceRows (k := k))
  exact h.congr fun Q hQ => covarianceValue_eq_rows Q hQ

end GaussianMeasureBridge
