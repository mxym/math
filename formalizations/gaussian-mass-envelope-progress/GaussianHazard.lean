import GaussianTail

/-!
The principal analytic lemma in the arbitrary-mass Gaussian centroid envelope.
The proof derives the derivative bounds from actual truncated Gaussian moments.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace GaussianMeasureBridge

/-- Upper Gaussian hazard parameterized by the actual threshold. -/
noncomputable def thresholdHazard (a : ℝ) : ℝ := standardDensity a / gaussianTail a

lemma thresholdHazard_pos (a : ℝ) : 0 < thresholdHazard a :=
  div_pos (standardDensity_pos a) (gaussianTail_pos a)

lemma thresholdHazard_mul_tail (a : ℝ) :
    thresholdHazard a * gaussianTail a = standardDensity a := by
  exact div_mul_cancel₀ _ (gaussianTail_pos a).ne'

lemma threshold_le_hazard (a : ℝ) : a ≤ thresholdHazard a := by
  exact (le_div_iff₀ (gaussianTail_pos a)).mpr (gaussianTail_threshold_le_firstMoment a)

/-- The upper derivative bound follows from the nonnegative conditional variance. -/
theorem thresholdHazard_variance_bound (a : ℝ) :
    thresholdHazard a * (thresholdHazard a - a) ≤ 1 := by
  have h := gaussianTail_centered_secondMoment_nonneg a (thresholdHazard a)
  rw [← thresholdHazard_mul_tail a] at h
  by_contra hbad
  have hn : 1 - thresholdHazard a * (thresholdHazard a - a) < 0 := by linarith
  have hnq := mul_neg_of_neg_of_pos hn (gaussianTail_pos a)
  nlinarith

lemma thresholdHazard_hasDerivAt (a : ℝ) :
    HasDerivAt thresholdHazard
      (thresholdHazard a * (thresholdHazard a - a)) a := by
  convert (standardDensity_hasDerivAt a).div (gaussianTail_hasDerivAt a)
    (gaussianTail_pos a).ne' using 1
  · rfl
  · unfold thresholdHazard
    field_simp [(gaussianTail_pos a).ne']
    ring

lemma thresholdHazard_monotone : Monotone thresholdHazard := by
  apply monotone_of_hasDerivAt_nonneg thresholdHazard_hasDerivAt
  intro a
  exact mul_nonneg (thresholdHazard_pos a).le (sub_nonneg.mpr (threshold_le_hazard a))

lemma squaredHazard_logTail_hasDerivAt (a : ℝ) :
    HasDerivAt (fun x => thresholdHazard x ^ 2 + 2 * Real.log (gaussianTail x))
      (2 * thresholdHazard a * (thresholdHazard a * (thresholdHazard a - a) - 1)) a := by
  have hl : HasDerivAt (fun x => Real.log (gaussianTail x)) (-thresholdHazard a) a := by
    simpa only [thresholdHazard, neg_div] using
      (gaussianTail_hasDerivAt a).log (gaussianTail_pos a).ne'
  convert ((thresholdHazard_hasDerivAt a).pow 2).add (hl.const_mul 2) using 1
  ring

lemma squaredHazard_logTail_antitone :
    Antitone (fun x => thresholdHazard x ^ 2 + 2 * Real.log (gaussianTail x)) := by
  apply antitone_of_hasDerivAt_nonpos squaredHazard_logTail_hasDerivAt
  intro a
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num) (thresholdHazard_pos a).le)
    (sub_nonpos.mpr (thresholdHazard_variance_bound a))

/-- Global squared-hazard bound in actual upper-tail probability, at arbitrary
real thresholds. Neither Gaussian moment identities nor a derivative estimate
are hypotheses of this theorem. -/
theorem squared_hazard_log_lipschitz_threshold (a b : ℝ) (hab : a ≤ b) :
    0 ≤ thresholdHazard b ^ 2 - thresholdHazard a ^ 2 ∧
    thresholdHazard b ^ 2 - thresholdHazard a ^ 2 ≤
      2 * Real.log (gaussianTail a / gaussianTail b) := by
  constructor
  · have hm := thresholdHazard_monotone hab
    have ha := (thresholdHazard_pos a).le
    have hb := (thresholdHazard_pos b).le
    nlinarith
  · have hm := squaredHazard_logTail_antitone hab
    rw [Real.log_div (gaussianTail_pos a).ne' (gaussianTail_pos b).ne']
    linarith

end GaussianMeasureBridge
