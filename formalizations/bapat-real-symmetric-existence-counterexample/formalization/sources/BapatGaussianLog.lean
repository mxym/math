import BapatOrthogonalSphere
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false
open MeasureTheory Set

namespace BapatRealExistence
noncomputable section

/-- A two-sided power bound controls the logarithmic singularity as well as the tail. -/
theorem abs_log_abs_le_half_powers (x : ℝ) :
    |Real.log (|x|)| ≤ 2*(|x|^(1/2:ℝ) + |x|^(-1/2:ℝ)) := by
  have h₁ := Real.log_le_rpow_div (abs_nonneg x) (by norm_num : (0:ℝ)<1/2)
  have h₂ := Real.log_le_rpow_div (inv_nonneg.mpr (abs_nonneg x))
    (by norm_num : (0:ℝ)<1/2)
  rw [Real.log_inv, ← Real.rpow_neg_eq_inv_rpow] at h₂
  rw [abs_le]
  constructor <;> nlinarith [Real.rpow_nonneg (abs_nonneg x) (1/2:ℝ),
    Real.rpow_nonneg (abs_nonneg x) (-1/2:ℝ)]

theorem integrable_even_of_integrableOn_Ioi {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioi 0)) (he : ∀ x, f (-x)=f x) : Integrable f := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0:ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_,hi⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def,he,neg_preimage,neg_Iio,neg_zero] using hi

theorem integrable_abs_rpow_gaussian {s : ℝ} (hs : -1<s) :
    Integrable (fun x : ℝ => |x|^s * Real.exp (-x^2)) := by
  apply integrable_even_of_integrableOn_Ioi
  · apply (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1) hs).congr_fun
    · intro x hx
      simp [abs_of_pos (show 0 < x from hx)]
    · exact measurableSet_Ioi
  · intro x
    simp

/-- Actual Lebesgue integrability of a logarithm against the real Gaussian weight. -/
theorem integrable_log_abs_gaussian :
    Integrable (fun x : ℝ => Real.log |x| * Real.exp (-x^2)) := by
  have hp := integrable_abs_rpow_gaussian (by norm_num : (-1:ℝ)<1/2)
  have hn := integrable_abs_rpow_gaussian (by norm_num : (-1:ℝ)< -1/2)
  apply ((hp.add hn).const_mul 2).mono'
  · have hl : Measurable (fun x : ℝ => Real.log |x|) :=
      Real.measurable_log.comp continuous_abs.measurable
    have he : Continuous (fun x : ℝ => Real.exp (-x^2)) := by fun_prop
    exact (hl.mul he.measurable).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_right (abs_log_abs_le_half_powers x)
      (Real.exp_pos (-x^2)).le
    dsimp only [Pi.add_apply]
    nlinarith

end
end BapatRealExistence
