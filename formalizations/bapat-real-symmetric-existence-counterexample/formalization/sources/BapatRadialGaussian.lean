import BapatGaussianLinear

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric

namespace BapatRealExistence
noncomputable section

theorem real_norm_integral (f : ℝ → ℝ) :
    (∫ x : ℝ, f |x|) = 2*∫ r in Ioi (0:ℝ), f r := by
  simpa [Real.norm_eq_abs,Module.finrank_self,Real.volume_real_ball (by norm_num : (0:ℝ)≤1),
    smul_eq_mul] using integral_fun_norm_addHaar (volume : Measure ℝ) f

theorem radial_gaussian_first_Ioi : (∫ r in Ioi (0:ℝ), r*Real.exp (-r^2)) = 1/2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := 1) (by norm_num) (by norm_num)
  simpa using h

theorem complex_gaussian_mass : (∫ z : ℂ, Real.exp (-‖z‖^2)) = Real.pi := by
  simpa using complex_radial_gaussian_integral 0

theorem complex_unit_ball_volume : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => Real.exp (-r^2))
  norm_num only [Complex.finrank_real_complex,smul_eq_mul,nsmul_eq_mul,show 2-1=1 by norm_num,pow_one,
    Nat.cast_ofNat,complex_gaussian_mass,radial_gaussian_first_Ioi] at h
  linarith

theorem complex_norm_integral (f : ℝ → ℝ) :
    (∫ z : ℂ, f ‖z‖) = (2*Real.pi)*∫ r in Ioi (0:ℝ), r*f r := by
  simpa only [Complex.finrank_real_complex,complex_unit_ball_volume,smul_eq_mul,nsmul_eq_mul,
    show 2-1=1 by norm_num,pow_one,Nat.cast_ofNat,mul_assoc] using
      integral_fun_norm_addHaar (volume : Measure ℂ) f

def radialPlaneGaussian (x y : ℝ) : ℝ := Real.sqrt (x^2+y^2)*Real.exp (-(x^2+y^2))

theorem radialPlaneGaussian_integrable : Integrable (fun p : ℝ × ℝ => radialPlaneGaussian p.1 p.2) := by
  rw [← Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding]
  convert complex_radial_gaussian_integrable 1 using 1
  ext z
  simp only [pow_one]
  change Real.sqrt (z.re^2+z.im^2)*Real.exp (-(z.re^2+z.im^2)) = ‖z‖*Real.exp (-‖z‖^2)
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.norm_def,Complex.normSq_apply,pow_two]

theorem radialPlaneGaussian_integral :
    (∫ x : ℝ, ∫ y : ℝ, radialPlaneGaussian x y) = Real.pi*Real.sqrt Real.pi/2 := by
  have hf := integral_prod (fun p : ℝ × ℝ => radialPlaneGaussian p.1 p.2) radialPlaneGaussian_integrable
  change (∫ p : ℝ × ℝ, radialPlaneGaussian p.1 p.2) = (∫ x : ℝ, ∫ y : ℝ, radialPlaneGaussian x y) at hf
  rw [← hf]
  rw [← Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding]
  convert complex_norm_gaussian_integral using 1
  congr 1
  ext z
  change Real.sqrt (z.re^2+z.im^2)*Real.exp (-(z.re^2+z.im^2)) = ‖z‖*Real.exp (-‖z‖^2)
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.norm_def,Complex.normSq_apply,pow_two]

/-- The positive quadrant contains one quarter of this even planar radial integral. -/
theorem radialPlaneGaussian_quadrant_integral :
    (∫ r in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), radialPlaneGaussian r s) =
      Real.pi*Real.sqrt Real.pi/8 := by
  have hin (x : ℝ) : (∫ y : ℝ, radialPlaneGaussian x y) =
      2*∫ s in Ioi (0:ℝ), radialPlaneGaussian x s := by
    simpa only [radialPlaneGaussian,sq_abs] using
      real_norm_integral (fun s => radialPlaneGaussian x s)
  have hout : (∫ x : ℝ, ∫ s in Ioi (0:ℝ), radialPlaneGaussian x s) =
      2*∫ r in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), radialPlaneGaussian r s := by
    simpa only [radialPlaneGaussian,sq_abs] using
      real_norm_integral (fun r => ∫ s in Ioi (0:ℝ), radialPlaneGaussian r s)
  have h := radialPlaneGaussian_integral
  simp_rw [hin] at h
  rw [integral_const_mul,hout] at h
  linarith

end
end BapatRealExistence
