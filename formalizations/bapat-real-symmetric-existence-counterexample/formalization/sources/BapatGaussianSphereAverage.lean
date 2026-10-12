import BapatGaussianLinear

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set

namespace BapatRealExistence
noncomputable section

theorem realFour_gaussian_mass : (∫ x : RealSpace4, Real.exp (-‖x‖^2)) = Real.pi^2 := by
  have h := realGaussian_coordinate_zero_integral (fun _ => 1)
  have hgauss : (∫ x : ℝ, Real.exp (-x^2)) = Real.sqrt Real.pi := by
    simpa only [neg_one_mul,div_one] using integral_gaussian (1:ℝ)
  simp only [one_mul,hgauss] at h
  rw [h]
  nlinarith [Real.sq_sqrt Real.pi_pos.le,sq_nonneg (Real.sqrt Real.pi)]

theorem homogeneous_zero_gaussian_sphere_area (f : RealSpace4 → ℝ)
    (hf : ∀ (r : ℝ), 0<r → ∀ x, f (r • x)=f x) :
    (∫ x : RealSpace4, f x*Real.exp (-‖x‖^2)) =
      (volume : Measure RealSpace4).toSphere.real univ / 2 *
        ∫ x : RealUnitSphere4, f x ∂normalizedSphere (volume : Measure RealSpace4) := by
  have h := homogeneous_gaussian_integral_even_dim (volume : Measure RealSpace4) 2 0
    (by norm_num) (by norm_num [RealSpace4])
    (fun x : RealSpace4 => (f x : ℂ))
    (by intro r hr x; simp only [hf r hr,mul_zero,pow_zero,one_mul])
  rw [integral_toSphere_eq_mass_mul_normalized] at h
  simp only [← Complex.ofReal_mul,integral_complex_ofReal] at h
  norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.factorial,Nat.cast_zero,Nat.cast_one] at h
  apply Complex.ofReal_injective
  push_cast
  convert h using 1 <;> push_cast <;> ring

theorem realFour_sphere_area : (volume : Measure RealSpace4).toSphere.real univ / 2 = Real.pi^2 := by
  have h := homogeneous_zero_gaussian_sphere_area (fun _ => 1) (by intros; rfl)
  simpa [one_mul,integral_const,measureReal_def,smul_eq_mul,mul_one,
    realFour_gaussian_mass] using h.symm

theorem homogeneous_zero_gaussian_sphere_average (f : RealSpace4 → ℝ)
    (hf : ∀ (r : ℝ), 0<r → ∀ x, f (r • x)=f x) :
    (∫ x : RealSpace4, f x*Real.exp (-‖x‖^2)) =
      Real.pi^2 * ∫ x : RealUnitSphere4, f x ∂normalizedSphere (volume : Measure RealSpace4) := by
  rw [homogeneous_zero_gaussian_sphere_area f hf,realFour_sphere_area]

/-- The separately homogeneous pair formula does not presume convergence of empirical moments. -/
theorem homogeneous_pair_gaussian_sphere_average (f : RealSpace4 → RealSpace4 → ℝ)
    (hf : ∀ (r : ℝ), 0<r → ∀ x y, f (r • x) y=f x y)
    (hg : ∀ (r : ℝ), 0<r → ∀ x y, f x (r • y)=f x y) :
    (∫ x : RealSpace4, ∫ y : RealSpace4, f x y*Real.exp (-‖y‖^2)*Real.exp (-‖x‖^2)) =
      Real.pi^4 * ∫ x : RealUnitSphere4, ∫ y : RealUnitSphere4, f x y
        ∂normalizedSphere (volume : Measure RealSpace4)
        ∂normalizedSphere (volume : Measure RealSpace4) := by
  have hi (x : RealSpace4) := homogeneous_zero_gaussian_sphere_average (f x)
    (by intro r hr y; exact hg r hr x y)
  simp_rw [integral_mul_const,hi]
  have ho := homogeneous_zero_gaussian_sphere_average
    (fun x => ∫ y : RealUnitSphere4, f x y ∂normalizedSphere (volume : Measure RealSpace4))
    (by intro r hr x; simp_rw [hf r hr])
  simp_rw [mul_assoc]
  rw [integral_const_mul,ho]
  ring

end
end BapatRealExistence
