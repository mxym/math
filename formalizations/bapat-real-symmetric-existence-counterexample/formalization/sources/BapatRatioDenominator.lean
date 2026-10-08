import BapatRatioCoordinates
import BapatRadialGaussian

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set

namespace BapatRealExistence
noncomputable section

theorem ratioDifferenceCoefficient_norm (d e : ℂ) :
    ‖ratioDifferenceCoefficient d e‖ = Real.sqrt (‖d‖⁻¹^2+‖e‖⁻¹^2) := by
  rw [← ratioDifferenceCoefficient_norm_sq,Real.sqrt_sq (norm_nonneg _)]

def ratioDenominatorKernel (d e : ℂ) : ℝ :=
  ‖ratioDifferenceCoefficient d e‖ * Real.exp (-(‖d‖^2+‖e‖^2))

theorem ratioDenominatorKernel_nonneg (d e : ℂ) : 0 ≤ ratioDenominatorKernel d e := by
  unfold ratioDenominatorKernel
  positivity

theorem ratioDenominatorKernel_integrable :
    Integrable (fun p : ℂ × ℂ => ratioDenominatorKernel p.1 p.2) := by
  have hg : Integrable (fun z : ℂ => Real.exp (-‖z‖^2)) := by
    simpa using complex_radial_gaussian_integrable 0
  have hi := (complex_inv_norm_gaussian_integrable.mul_prod hg).add
    (hg.mul_prod complex_inv_norm_gaussian_integrable)
  apply hi.mono' (by unfold ratioDenominatorKernel; simp_rw [ratioDifferenceCoefficient_norm]; fun_prop)
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (ratioDenominatorKernel_nonneg p.1 p.2)]
  calc
    _ ≤ (‖p.1‖⁻¹+‖p.2‖⁻¹)*Real.exp (-(‖p.1‖^2+‖p.2‖^2)) :=
      mul_le_mul_of_nonneg_right (ratioDifferenceCoefficient_norm_le _ _) (Real.exp_pos _).le
    _ = _ := by dsimp only [Pi.add_apply]; rw [neg_add,Real.exp_add]; ring

theorem positive_radial_cancel (r s : ℝ) (hr : 0<r) (hs : 0<s) :
    r*s*Real.sqrt (r⁻¹^2+s⁻¹^2) = Real.sqrt (r^2+s^2) := by
  have h : (r*s*Real.sqrt (r⁻¹^2+s⁻¹^2))^2 = r^2+s^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
    field_simp
    <;> ring
  nlinarith [Real.sq_sqrt (show 0≤r^2+s^2 by positivity),
    Real.sqrt_nonneg (r^2+s^2),show 0≤r*s*Real.sqrt (r⁻¹^2+s⁻¹^2) by positivity]

/-- Direct evaluation after cancellation of both planar radial Jacobians. -/
theorem ratioDenominatorKernel_integral :
    (∫ d : ℂ, ∫ e : ℂ, ratioDenominatorKernel d e) = Real.pi^3*Real.sqrt Real.pi/2 := by
  let f (r s : ℝ) := Real.sqrt (r⁻¹^2+s⁻¹^2)*Real.exp (-(r^2+s^2))
  have he (d : ℂ) : (∫ e : ℂ, ratioDenominatorKernel d e) =
      (2*Real.pi)*∫ s in Ioi (0:ℝ), s*f ‖d‖ s := by
    simpa only [ratioDenominatorKernel,ratioDifferenceCoefficient_norm,f] using
      complex_norm_integral (fun s => f ‖d‖ s)
  simp_rw [he]
  rw [integral_const_mul]
  have hd := complex_norm_integral (fun r => ∫ s in Ioi (0:ℝ), s*f r s)
  rw [hd]
  have hc : (∫ r in Ioi (0:ℝ), r * ∫ s in Ioi (0:ℝ), s*f r s) =
      ∫ r in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), radialPlaneGaussian r s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp [f,radialPlaneGaussian]
    rw [← mul_assoc,← mul_assoc,positive_radial_cancel r s hr hs]
  rw [hc,radialPlaneGaussian_quadrant_integral]
  ring

theorem ratioDenominatorKernel_prod_integral :
    (∫ p : ℂ × ℂ, ratioDenominatorKernel p.1 p.2) = Real.pi^3*Real.sqrt Real.pi/2 := by
  have h := integral_prod (fun p : ℂ × ℂ => ratioDenominatorKernel p.1 p.2) ratioDenominatorKernel_integrable
  change (∫ p : ℂ × ℂ, ratioDenominatorKernel p.1 p.2) =
    (∫ d : ℂ, ∫ e : ℂ, ratioDenominatorKernel d e) at h
  rw [h,ratioDenominatorKernel_integral]

end
end BapatRealExistence
