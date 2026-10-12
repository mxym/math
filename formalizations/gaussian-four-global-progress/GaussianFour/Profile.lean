import GaussianQuantile
import Mathlib.Analysis.Real.Pi.Bounds

/-! Strict Gaussian profile bounds for the four-cell singular boundary. -/
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace GaussianFour
open GaussianMeasureBridge

noncomputable def quarterQuantile : ℝ := upperQuantile (1 / 4)
noncomputable def quarterDensity : ℝ := standardDensity quarterQuantile

lemma standardDensity_neg (x : ℝ) : standardDensity (-x) = standardDensity x := by
  simp [standardDensity_eq]

lemma gaussianTail_neg (a : ℝ) : gaussianTail (-a) = 1 - gaussianTail a := by
  have hsum := integral_add_compl (μ := volume) (s := Ioi a)
    (f := standardDensity) measurableSet_Ioi integrable_standardDensity
  rw [compl_Ioi, show (∫ x, standardDensity x) = 1 from
    integral_gaussianPDFReal_eq_one 0 one_ne_zero] at hsum
  have he : (∫ x in Iic a, standardDensity x) = gaussianTail (-a) := by
    simpa only [neg_neg, standardDensity_neg, gaussianTail] using
      (integral_comp_neg_Ioi (-a) standardDensity).symm
  rw [he] at hsum
  change gaussianTail a + gaussianTail (-a) = 1 at hsum
  linarith

lemma gaussianTail_zero : gaussianTail 0 = 1 / 2 := by
  have h := gaussianTail_neg 0
  norm_num only [neg_zero] at h
  linarith

lemma quarterQuantile_tail : gaussianTail quarterQuantile = 1 / 4 :=
  gaussianTail_upperQuantile (by norm_num) (by norm_num)

lemma quarterQuantile_pos : 0 < quarterQuantile := by
  by_contra h
  have hm := gaussianTail_strictAnti.antitone (le_of_not_gt h)
  rw [quarterQuantile_tail, gaussianTail_zero] at hm
  norm_num at hm

lemma standardDensity_zero_gt : (39 / 100 : ℝ) < standardDensity 0 := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_lt_d2
  have hbound : Real.sqrt (2 * Real.pi) < 100 / 39 := by nlinarith
  simp only [standardDensity_eq, zero_pow (by decide : 2 ≠ 0), neg_zero,
    zero_div, Real.exp_zero, mul_one, inv_eq_one_div]
  apply (lt_div_iff₀ hs).2
  nlinarith

lemma standardDensity_quadratic_lower (x : ℝ) :
    standardDensity 0 * (1 - x ^ 2 / 2) ≤ standardDensity x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(x ^ 2) / 2))
    (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))
  simpa [standardDensity_eq, sub_eq_add_neg, add_comm, neg_div] using h

lemma integral_quadratic_lower (a : ℝ) :
    (∫ x in 0..a, standardDensity 0 * (1 - x ^ 2 / 2)) =
      standardDensity 0 * (a - a ^ 3 / 6) := by
  have hd : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => standardDensity 0 * (y - y ^ 3 / 6))
      (standardDensity 0 * (1 - x ^ 2 / 2)) x := by
    intro x
    convert ((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 6)).const_mul
      (standardDensity 0) using 1 <;> dsimp <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc 0 a) => hd x)
    (show IntervalIntegrable (fun x : ℝ => standardDensity 0 * (1 - x ^ 2 / 2))
      volume 0 a from (by fun_prop : Continuous _).intervalIntegrable _ _)
  simpa using h

/-- An analytic rational upper bound for the actual upper Gaussian quartile. -/
theorem quarterQuantile_lt_seven_tenths : quarterQuantile < 7 / 10 := by
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 7 / 10)
    (show IntervalIntegrable (fun x : ℝ => standardDensity 0 * (1 - x ^ 2 / 2))
      volume 0 (7 / 10) from (by fun_prop : Continuous _).intervalIntegrable _ _)
    (integrable_standardDensity.intervalIntegrable (a := 0) (b := 7 / 10))
    (fun x _ => standardDensity_quadratic_lower x)
  rw [integral_quadratic_lower] at hi
  have ht := gaussianTail_sub_eq_interval 0 (7 / 10)
  rw [gaussianTail_zero] at ht
  have hs := standardDensity_zero_gt
  have htail : gaussianTail (7 / 10) < 1 / 4 := by norm_num at hi; nlinarith
  by_contra hq
  have hm := gaussianTail_strictAnti.antitone (le_of_not_gt hq)
  rw [quarterQuantile_tail] at hm
  linarith

/-- The strict profile ratio used for the middle rank-one interface. -/
theorem quarterDensity_gt_three_quarters :
    (3 / 4 : ℝ) * standardDensity 0 < quarterDensity := by
  have hq0 := quarterQuantile_pos
  have hq1 := quarterQuantile_lt_seven_tenths
  have hs := standardDensity_pos 0
  have hl := standardDensity_quadratic_lower quarterQuantile
  have hq2 : quarterQuantile ^ 2 < 49 / 100 := by nlinarith
  have hm := mul_pos hs (show 0 < 1 / 4 - quarterQuantile ^ 2 / 2 by linarith)
  change _ < standardDensity quarterQuantile
  nlinarith

lemma quarterDensity_pos : 0 < quarterDensity := standardDensity_pos _

lemma quarterDensity_lt_center : quarterDensity < standardDensity 0 := by
  have hq := quarterQuantile_pos
  have he : Real.exp (-(quarterQuantile ^ 2) / 2) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have hs : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  simpa [quarterDensity, standardDensity_eq] using mul_lt_mul_of_pos_left he hs

lemma standardDensity_zero_sq : standardDensity 0 ^ 2 = 1 / (2 * Real.pi) := by
  simp only [standardDensity_eq, zero_pow (by decide : 2 ≠ 0), neg_zero,
    zero_div, Real.exp_zero, mul_one, inv_pow]
  rw [Real.sq_sqrt (by positivity)]
  simp only [one_div]

/-- The exact strict profile-versus-three-cell margin. -/
theorem quarterDensity_sq_gt_three_cell_quarter :
    (9 : ℝ) / (32 * Real.pi) < quarterDensity ^ 2 := by
  have h := quarterDensity_gt_three_quarters
  have hs := standardDensity_pos 0
  have hh := quarterDensity_pos
  have hsq : (9 / 16 : ℝ) * standardDensity 0 ^ 2 < quarterDensity ^ 2 := by
    nlinarith
  rw [standardDensity_zero_sq] at hsq
  convert hsq using 1 <;> field_simp <;> ring

end GaussianFour
