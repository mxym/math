import GaussianCovarianceContinuity

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

/-- The trace-one centered covariance domain used by the geometric comparison. -/
def NormalizedCovariance (Q : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Q.PosSemidef ∧ (∀ i, ∑ j, Q i j = 0) ∧ Q.trace = 1

namespace FractionalPartition

lemma scoreGram_moment_centered (F : FractionalPartition d k) (i : Fin k) :
    ∑ j, scoreGram F.moment i j = 0 := by
  simp only [scoreGram, ← inner_sum, F.sum_moment, inner_zero_right]

lemma trace_scoreGram_moment (F : FractionalPartition d k) :
    (scoreGram F.moment).trace = F.momentEnergy := by
  simp only [Matrix.trace, Matrix.diag, scoreGram, real_inner_self_eq_norm_sq, momentEnergy]

noncomputable def normalizedMomentCovariance (F : FractionalPartition d k) :
    Matrix (Fin k) (Fin k) ℝ := F.momentEnergy⁻¹ • scoreGram F.moment

/-- Every nonzero actual moment family produces an element of the paper's
normalized covariance domain. -/
theorem normalizedMomentCovariance_mem (F : FractionalPartition d k)
    (hF : 0 < F.momentEnergy) : NormalizedCovariance F.normalizedMomentCovariance := by
  refine ⟨(scoreGram_posSemidef F.moment).smul (inv_nonneg.mpr hF.le), ?_, ?_⟩
  · intro i
    simp only [normalizedMomentCovariance, Matrix.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, F.scoreGram_moment_centered, mul_zero]
  · rw [normalizedMomentCovariance, Matrix.trace_smul, F.trace_scoreGram_moment]
    exact inv_mul_cancel₀ hF.ne'

/-- The actual covariance bound is equivalent to a normalized one by the
proved square-root homogeneity; no rank assumption is present. -/
theorem equalMassValue_moment_normalize (F : FractionalPartition d k)
    (hF : 0 < F.momentEnergy) :
    equalMassValue F.moment = Real.sqrt F.momentEnergy *
      covarianceValue F.normalizedMomentCovariance := by
  have hm : F.momentEnergy • F.normalizedMomentCovariance = scoreGram F.moment := by
    rw [normalizedMomentCovariance, smul_smul, mul_inv_cancel₀ hF.ne', one_smul]
  rw [← covarianceValue_scoreGram, ← hm,
    covarianceValue_smul _ (F.normalizedMomentCovariance_mem hF).1 _ hF.le]

/-- Explicit reduction theorem, not the unresolved geometric comparison.
The hypothesis is deliberately the remaining bound on the actual covariance
value, and is never registered as an axiom or presented as a full solution. -/
theorem momentEnergy_bound_of_normalized_covariance_bound
    (F : FractionalPartition d k) (hF : ∀ i, F.mass i = uniformMass k i)
    (c : ℝ) (hc : 0 ≤ c)
    (hgeom : ∀ Q : Matrix (Fin k) (Fin k) ℝ,
      NormalizedCovariance Q → covarianceValue Q ≤ c) :
    F.momentEnergy ≤ c ^ 2 := by
  rcases F.momentEnergy_nonneg.eq_or_lt with hz | hpos
  · rw [← hz]
    exact sq_nonneg c
  · apply F.momentEnergy_le_sq_of_score_bound hF c hc
    rw [F.equalMassValue_moment_normalize hpos, mul_comm c]
    exact mul_le_mul_of_nonneg_left
      (hgeom _ (F.normalizedMomentCovariance_mem hpos)) (Real.sqrt_nonneg _)

end FractionalPartition
end GaussianMeasureBridge
