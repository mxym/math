import GaussianHalflineFlux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
Actual standard Gaussian upper-tail calculus for the mass-envelope theorem.
All moments below are Lebesgue integrals of the actual Gaussian density.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace GaussianMeasureBridge

lemma integrable_standardDensity : Integrable standardDensity :=
  integrable_gaussianPDFReal 0 1

lemma continuous_standardDensity : Continuous standardDensity :=
  continuous_iff_continuousAt.mpr fun x => (standardDensity_hasDerivAt x).continuousAt

/-- The actual standard Gaussian upper-tail probability, represented by its density. -/
noncomputable def gaussianTail (a : ℝ) : ℝ := ∫ x in Ioi a, standardDensity x

lemma gaussianTail_nonneg (a : ℝ) : 0 ≤ gaussianTail a :=
  integral_nonneg fun x => (standardDensity_pos x).le

lemma gaussianTail_pos (a : ℝ) : 0 < gaussianTail a := by
  unfold gaussianTail
  rw [integral_pos_iff_support_of_nonneg
    (fun x => (standardDensity_pos x).le) integrable_standardDensity.integrableOn]
  have hs : Function.support standardDensity = univ := by
    ext x
    simp [Function.mem_support, (standardDensity_pos x).ne']
  rw [hs]
  simp

lemma gaussianTail_eq_probability (a : ℝ) :
    gaussianTail a = ((gaussianReal 0 1) (Ioi a)).toReal := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  exact (ENNReal.toReal_ofReal (gaussianTail_nonneg a)).symm

lemma gaussianTail_lt_one (a : ℝ) : gaussianTail a < 1 := by
  have hpos : 0 < ∫ x in Iic a, standardDensity x := by
    rw [integral_pos_iff_support_of_nonneg
      (fun x => (standardDensity_pos x).le) integrable_standardDensity.integrableOn]
    have hs : Function.support standardDensity = univ := by
      ext x
      simp [Function.mem_support, (standardDensity_pos x).ne']
    rw [hs]
    simp
  have hsum := integral_add_compl (μ := volume) (s := Ioi a)
    (f := standardDensity) measurableSet_Ioi integrable_standardDensity
  rw [compl_Ioi] at hsum
  have hone : (∫ x, standardDensity x) = 1 :=
    integral_gaussianPDFReal_eq_one 0 one_ne_zero
  rw [hone] at hsum
  change gaussianTail a + _ = 1 at hsum
  linarith

lemma gaussianTail_sub_eq_interval (a b : ℝ) :
    gaussianTail a - gaussianTail b = ∫ x in a..b, standardDensity x :=
  intervalIntegral.integral_Ioi_sub_Ioi'
    integrable_standardDensity.integrableOn integrable_standardDensity.integrableOn

lemma gaussianTail_hasDerivAt (a : ℝ) :
    HasDerivAt gaussianTail (-standardDensity a) a := by
  have h := (intervalIntegral.integral_hasDerivAt_right
    (integrable_standardDensity.intervalIntegrable (a := 0) (b := a))
    continuous_standardDensity.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_standardDensity.continuousAt).const_sub (gaussianTail 0)
  have he : (fun b => gaussianTail 0 - ∫ x in 0..b, standardDensity x) = gaussianTail := by
    funext b
    linarith [gaussianTail_sub_eq_interval 0 b]
  rwa [he] at h

lemma gaussianTail_tendsto_zero : Tendsto gaussianTail atTop (𝓝 0) :=
  tendsto_integral_Ioi_zero tendsto_id

lemma integrable_sq_mul_standardDensity :
    Integrable (fun x : ℝ => x ^ 2 * standardDensity x) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (-1 : ℝ) < 2)).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1
  ext x
  rw [standardDensity_eq, Real.rpow_two]
  have he : -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2) / 2 := by ring
  rw [he]
  ring

lemma mul_standardDensity_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => y * standardDensity y)
      (standardDensity x - x ^ 2 * standardDensity x) x := by
  convert (hasDerivAt_id x).mul (standardDensity_hasDerivAt x) using 1
  · rfl
  · simp only [id_eq]
    ring

lemma mul_standardDensity_tendsto_zero :
    Tendsto (fun x => x * standardDensity x) atTop (𝓝 0) := by
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => mul_standardDensity_hasDerivAt x)
    (integrable_standardDensity.sub integrable_sq_mul_standardDensity).integrableOn
    integrable_mul_standardDensity.integrableOn

/-- The exact unnormalized second moment of a truncated standard Gaussian. -/
theorem gaussianTail_secondMoment (a : ℝ) :
    (∫ x in Ioi a, x ^ 2 * standardDensity x) = gaussianTail a + a * standardDensity a := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := a)
    (fun x _ => mul_standardDensity_hasDerivAt x)
    (integrable_standardDensity.sub integrable_sq_mul_standardDensity).integrableOn
    mul_standardDensity_tendsto_zero
  rw [integral_sub integrable_standardDensity.integrableOn
    integrable_sq_mul_standardDensity.integrableOn] at h
  change gaussianTail a - _ = 0 - a * standardDensity a at h
  linarith

/-- The upper-tail first moment is at least its threshold times its mass. -/
theorem gaussianTail_threshold_le_firstMoment (a : ℝ) :
    a * gaussianTail a ≤ standardDensity a := by
  have h := integral_mono_ae
    (integrable_standardDensity.const_mul a).integrableOn
    integrable_mul_standardDensity.integrableOn
    (show (fun x => a * standardDensity x) ≤ᵐ[volume.restrict (Ioi a)]
      (fun x => x * standardDensity x) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_le_mul_of_nonneg_right hx.le (standardDensity_pos x).le)
  rw [integral_const_mul, integral_Ioi_mul_standardDensity] at h
  exact h

/-- Nonnegativity of the actual truncated centered square, without any variance assumption. -/
theorem gaussianTail_centered_secondMoment_nonneg (a c : ℝ) :
    0 ≤ gaussianTail a + a * standardDensity a - 2 * c * standardDensity a +
      c ^ 2 * gaussianTail a := by
  have hnon : 0 ≤ ∫ x in Ioi a, (x - c) ^ 2 * standardDensity x :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (standardDensity_pos x).le
  have he : (fun x => (x - c) ^ 2 * standardDensity x) =
      (fun x => x ^ 2 * standardDensity x - (2 * c) * (x * standardDensity x) +
        c ^ 2 * standardDensity x) := by funext x; ring
  have hi₁ : IntegrableOn (fun x : ℝ => x ^ 2 * standardDensity x -
      (2 * c) * (x * standardDensity x)) (Ioi a) :=
    (integrable_sq_mul_standardDensity.sub
      (integrable_mul_standardDensity.const_mul (2 * c))).integrableOn
  have hi₂ : IntegrableOn (fun x : ℝ => c ^ 2 * standardDensity x) (Ioi a) :=
    (integrable_standardDensity.const_mul (c ^ 2)).integrableOn
  rw [he, integral_add hi₁ hi₂,
    integral_sub integrable_sq_mul_standardDensity.integrableOn
      (integrable_mul_standardDensity.const_mul (2 * c)).integrableOn,
    integral_const_mul, integral_const_mul,
    gaussianTail_secondMoment, integral_Ioi_mul_standardDensity] at hnon
  exact hnon

end GaussianMeasureBridge
