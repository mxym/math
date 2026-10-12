import GaussianQuantile

/-!
The terminal-cell estimate in the Gaussian mass-envelope theorem.
An integrated exponential tangent proves the conditional Jensen bound directly.
-/
open MeasureTheory ProbabilityTheory Set

namespace GaussianMeasureBridge

lemma gaussianTail_exp_moment_bound (a : ℝ) :
    gaussianTail a * Real.exp (thresholdHazard a ^ 2) ≤
      Real.exp (thresholdHazard a ^ 2 / 2) := by
  let t := thresholdHazard a
  let μ := gaussianReal 0 1
  have hi : Integrable (fun x : ℝ => x) μ := IsGaussian.integrable_id
  have he : Integrable (fun x : ℝ => Real.exp (t * x)) μ :=
    integrable_exp_mul_gaussianReal t
  have haff : Integrable (fun x : ℝ => Real.exp (t ^ 2) * (1 + t * x - t ^ 2)) μ :=
    (((integrable_const 1).add (hi.const_mul t)).sub (integrable_const (t ^ 2))).const_mul _
  have hpoint : ∀ x : ℝ,
      (Ioi a).indicator (fun x => Real.exp (t ^ 2) * (1 + t * x - t ^ 2)) x ≤
        Real.exp (t * x) := by
    intro x
    by_cases hx : x ∈ Ioi a
    · rw [indicator_of_mem hx]
      calc
        Real.exp (t ^ 2) * (1 + t * x - t ^ 2) =
          Real.exp (t ^ 2) * ((t * x - t ^ 2) + 1) := by ring
        _ ≤ Real.exp (t ^ 2) * Real.exp (t * x - t ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
        _ = Real.exp (t * x) := by rw [← Real.exp_add]; congr 1; ring
    · rw [indicator_of_notMem hx]
      exact (Real.exp_pos _).le
  have h := integral_mono_ae (haff.indicator measurableSet_Ioi) he (ae_of_all _ hpoint)
  rw [integral_indicator measurableSet_Ioi, integral_const_mul] at h
  have hinside : (∫ x in Ioi a, (1 : ℝ) + t * x - t ^ 2 ∂μ) = gaussianTail a := by
    have hsum : IntegrableOn (fun x : ℝ => 1 + t * x) (Ioi a) μ :=
      ((integrable_const 1).add (hi.const_mul t)).integrableOn
    rw [integral_sub hsum (integrable_const (t ^ 2)).integrableOn,
      integral_add (integrable_const 1).integrableOn (hi.const_mul t).integrableOn,
      integral_const_mul, gaussianReal_halfline_firstMoment,
      integral_const, integral_const]
    simp only [smul_eq_mul, mul_one]
    change (((gaussianReal 0 1).restrict (Ioi a)) univ).toReal + t * standardDensity a -
      (((gaussianReal 0 1).restrict (Ioi a)) univ).toReal * t ^ 2 = gaussianTail a
    simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [← gaussianTail_eq_probability a]
    rw [← thresholdHazard_mul_tail a]
    dsimp [t]
    ring
  have hmgf : (∫ x : ℝ, Real.exp (t * x) ∂μ) = Real.exp (t ^ 2 / 2) := by
    simpa [mgf, μ] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) t
  rw [hinside, hmgf] at h
  simpa [t, mul_comm] using h

/-- The hazard squared is at most twice the log inverse tail mass, for every threshold. -/
theorem gaussianTail_hazard_entropy_bound (a : ℝ) :
    thresholdHazard a ^ 2 ≤ 2 * Real.log (1 / gaussianTail a) := by
  have h := Real.log_le_log
    (mul_pos (gaussianTail_pos a) (Real.exp_pos _)) (gaussianTail_exp_moment_bound a)
  rw [Real.log_mul (gaussianTail_pos a).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp] at h
  rw [Real.log_div one_ne_zero (gaussianTail_pos a).ne', Real.log_one]
  linarith

/-- Paper equation (16b), with the actual quantile rather than an assumed Gaussian profile. -/
theorem gaussian_profile_entropy_bound {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    standardDensity (upperQuantile p) ^ 2 ≤ 2 * p ^ 2 * Real.log (1 / p) := by
  have h := gaussianTail_hazard_entropy_bound (upperQuantile p)
  rw [gaussianTail_upperQuantile hp hp1,
    ← massHazard_eq_thresholdHazard hp hp1] at h
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg p)
  have he : p ^ 2 * massHazard p ^ 2 = standardDensity (upperQuantile p) ^ 2 := by
    unfold massHazard
    field_simp [hp.ne']
  rw [he] at hmul
  nlinarith

end GaussianMeasureBridge
