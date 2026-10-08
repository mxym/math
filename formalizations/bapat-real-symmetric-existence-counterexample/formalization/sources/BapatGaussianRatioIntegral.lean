import BapatRatioDenominator

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set

namespace BapatRealExistence
noncomputable section

theorem realFour_norm_gaussian_integrable :
    Integrable (fun x : RealSpace4 => ‖x‖*Real.exp (-‖x‖^2)) := by
  apply ((integrable_realGaussian_weight (ι := Fin 4)).add integrable_realGaussian_norm_sq).mono'
    (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
  convert mul_le_mul_of_nonneg_right h (Real.exp_pos (-‖x‖^2)).le using 1 <;>
    simp only [Pi.add_apply] <;> ring

def gaussianRatioKernel (d e : ℂ) (x : RealSpace4) : ℝ :=
  |inner ℝ (ratioDifferenceCoefficient d e) x| * Real.exp (-‖x‖^2) *
    Real.exp (-(‖d‖^2+‖e‖^2))

theorem gaussianRatioKernel_nonneg (d e : ℂ) (x : RealSpace4) :
    0 ≤ gaussianRatioKernel d e x := by unfold gaussianRatioKernel; positivity

theorem gaussianRatioKernel_measurable :
    Measurable (fun p : (ℂ × ℂ) × RealSpace4 => gaussianRatioKernel p.1.1 p.1.2 p.2) := by
  unfold gaussianRatioKernel
  simp_rw [ratioDifferenceCoefficient_inner]
  unfold complexPair
  fun_prop

theorem gaussianRatioKernel_integrable :
    Integrable (fun p : (ℂ × ℂ) × RealSpace4 => gaussianRatioKernel p.1.1 p.1.2 p.2) := by
  apply (ratioDenominatorKernel_integrable.mul_prod realFour_norm_gaussian_integrable).mono'
    gaussianRatioKernel_measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (gaussianRatioKernel_nonneg _ _ _)]
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm (ratioDifferenceCoefficient p.1.1 p.1.2) p.2)
      (Real.exp_pos (-‖p.2‖^2)).le)
    (Real.exp_pos (-(‖p.1.1‖^2+‖p.1.2‖^2))).le
  convert h using 1 <;> dsimp only [gaussianRatioKernel,ratioDenominatorKernel] <;> ring

theorem gaussianRatioKernel_inner_integral (d e : ℂ) :
    (∫ x : RealSpace4, gaussianRatioKernel d e x) =
      Real.pi*Real.sqrt Real.pi*ratioDenominatorKernel d e := by
  unfold gaussianRatioKernel ratioDenominatorKernel
  rw [integral_mul_const,real_four_gaussian_abs_inner_integral]
  ring

/-- Unnormalised eight-dimensional Gaussian absolute ratio-difference integral. -/
theorem gaussianRatioKernel_integral :
    (∫ p : (ℂ × ℂ) × RealSpace4, gaussianRatioKernel p.1.1 p.1.2 p.2) = Real.pi^5/2 := by
  rw [Measure.volume_eq_prod,integral_prod _ gaussianRatioKernel_integrable]
  simp_rw [gaussianRatioKernel_inner_integral]
  rw [integral_const_mul,ratioDenominatorKernel_prod_integral]
  calc
    _ = Real.pi^4*(Real.sqrt Real.pi)^2/2 := by ring
    _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]; ring

end
end BapatRealExistence
