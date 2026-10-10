import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Exact triangular-cap integration for the pair-separation step of the balanced
four-cell Gaussian proof. All integrals use actual Lebesgue/Gaussian measures.
-/

open MeasureTheory ProbabilityTheory Set

namespace GaussianFour

noncomputable def tent (r t x : ℝ) : ℝ := max (r - |x - t|) 0

lemma tent_nonneg (r t x : ℝ) : 0 ≤ tent r t x := le_max_right _ _

lemma tent_le_radius {r : ℝ} (hr : 0 ≤ r) (t x : ℝ) : tent r t x ≤ r := by
  exact max_le (sub_le_self _ (abs_nonneg _)) hr

lemma continuous_tent (r t : ℝ) : Continuous (tent r t) := by
  unfold tent
  fun_prop

lemma tent_eq_ramps {r : ℝ} (hr : 0 ≤ r) (t x : ℝ) :
    tent r t x =
      (Ioc (t-r) t).indicator (fun y : ℝ => r + (y-t)) x +
      (Ioc t (t+r)).indicator (fun y : ℝ => r - (y-t)) x := by
  classical
  by_cases hxt : x ≤ t
  · have ha : |x-t| = t-x := by rw [abs_of_nonpos (sub_nonpos.mpr hxt)]; ring
    by_cases hleft : t-r < x
    · have hmem : x ∈ Ioc (t-r) t := ⟨hleft,hxt⟩
      have hnot : x ∉ Ioc t (t+r) := fun h => (not_lt_of_ge hxt) h.1
      simp only [tent, ha, indicator_of_mem hmem, indicator_of_notMem hnot, add_zero]
      rw [max_eq_left (by linarith)]
      ring
    · have hnot : x ∉ Ioc (t-r) t := fun h => hleft h.1
      have hnot' : x ∉ Ioc t (t+r) := fun h => (not_lt_of_ge hxt) h.1
      simp only [tent, ha, indicator_of_notMem hnot, indicator_of_notMem hnot', add_zero]
      exact max_eq_right (by linarith)
  · have htx : t < x := lt_of_not_ge hxt
    have ha : |x-t| = x-t := abs_of_nonneg (sub_nonneg.mpr htx.le)
    have hnot : x ∉ Ioc (t-r) t := fun h => hxt h.2
    by_cases hright : x ≤ t+r
    · have hmem : x ∈ Ioc t (t+r) := ⟨htx,hright⟩
      simp only [tent, ha, indicator_of_notMem hnot, indicator_of_mem hmem, zero_add]
      exact max_eq_left (by linarith)
    · have hnot' : x ∉ Ioc t (t+r) := fun h => hright h.2
      simp only [tent, ha, indicator_of_notMem hnot, indicator_of_notMem hnot', add_zero]
      exact max_eq_right (by linarith)

lemma integrable_tent {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : Integrable (tent r t) := by
  have hl : IntegrableOn (fun y : ℝ => r+(y-t)) (Ioc (t-r) t) :=
    (show Continuous (fun y : ℝ => r+(y-t)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hu : IntegrableOn (fun y : ℝ => r-(y-t)) (Ioc t (t+r)) :=
    (show Continuous (fun y : ℝ => r-(y-t)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h := (hl.indicator measurableSet_Ioc).add (hu.indicator measurableSet_Ioc)
  exact h.congr (ae_of_all _ fun x => (tent_eq_ramps hr t x).symm)

/-- The Lebesgue integral of a triangular cap is exactly the square of its radius. -/
theorem integral_tent {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : ∫ x, tent r t x = r^2 := by
  have hl : IntervalIntegrable (fun y : ℝ => r+(y-t)) volume (t-r) t :=
    (show Continuous (fun y : ℝ => r+(y-t)) by fun_prop).intervalIntegrable _ _
  have hu : IntervalIntegrable (fun y : ℝ => r-(y-t)) volume t (t+r) :=
    (show Continuous (fun y : ℝ => r-(y-t)) by fun_prop).intervalIntegrable _ _
  have hlo : t-r ≤ t := sub_le_self _ hr
  have hhi : t ≤ t+r := le_add_of_nonneg_right hr
  have hli := hl.1.indicator measurableSet_Ioc
  have hui := hu.1.indicator measurableSet_Ioc
  simp_rw [tent_eq_ramps hr t]
  rw [integral_add hli hui, integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hlo,
    ← intervalIntegral.integral_of_le hhi]
  rw [intervalIntegral.integral_add intervalIntegrable_const
        (intervalIntegrable_id.sub intervalIntegrable_const),
    intervalIntegral.integral_sub intervalIntegrable_id intervalIntegrable_const,
    intervalIntegral.integral_sub intervalIntegrable_const
        (intervalIntegrable_id.sub intervalIntegrable_const),
    intervalIntegral.integral_sub intervalIntegrable_id intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_id, smul_eq_mul]
  ring

/-- The exact supremum of the standard real Gaussian density. -/
noncomputable def densityBound : ℝ := (Real.sqrt (2 * Real.pi))⁻¹

lemma densityBound_pos : 0 < densityBound := by
  unfold densityBound
  positivity

lemma gaussianPDF_le_densityBound (x : ℝ) : gaussianPDFReal 0 1 x ≤ densityBound := by
  have he : Real.exp (-x^2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by positivity)
  simpa [gaussianPDFReal, densityBound] using
    mul_le_mul_of_nonneg_left he densityBound_pos.le

/-- A Gaussian cap has integral at most density supremum times its exact area. -/
theorem gaussian_integral_tent_le {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    (∫ x, tent r t x ∂gaussianReal 0 1) ≤ densityBound * r^2 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  have ht := integrable_tent hr t
  have hprod : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * tent r t x) := by
    apply (ht.const_mul densityBound).mono' (by fun_prop)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (tent_nonneg _ _ _))]
      exact mul_le_mul_of_nonneg_right (gaussianPDF_le_densityBound x) (tent_nonneg _ _ _)
  have hle := integral_mono hprod (ht.const_mul densityBound) (fun x =>
    mul_le_mul_of_nonneg_right (gaussianPDF_le_densityBound x) (tent_nonneg _ _ _))
  simpa only [integral_const_mul, integral_tent hr t] using hle

end GaussianFour
