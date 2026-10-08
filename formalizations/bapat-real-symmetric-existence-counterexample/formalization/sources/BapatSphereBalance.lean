import BapatGaussianBalance

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set

namespace BapatRealExistence
noncomputable section

def sphereCanonicalPotential (t : ℝ) : ℝ :=
  ∫ x : RealUnitSphere4, canonicalPotential t x ∂normalizedSphere (volume : Measure RealSpace4)

theorem canonicalPotential_gaussian_sphere_integral (t : ℝ) :
    (∫ x : RealSpace4, canonicalPotential t x * Real.exp (-‖x‖^2)) =
      (volume : Measure RealSpace4).toSphere.real univ / 2 * sphereCanonicalPotential t := by
  have h := homogeneous_gaussian_integral_even_dim (volume : Measure RealSpace4) 2 0
    (by norm_num) (by norm_num [RealSpace4])
    (fun x : RealSpace4 => (canonicalPotential t x : ℂ))
    (by intro a ha x; simp only [canonicalPotential_smul t a ha, mul_zero,pow_zero,one_mul])
  rw [integral_toSphere_eq_mass_mul_normalized] at h
  simp only [← Complex.ofReal_mul,integral_complex_ofReal] at h
  norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.factorial,Nat.cast_zero,Nat.cast_one] at h
  apply Complex.ofReal_injective
  push_cast
  convert h using 1 <;> dsimp only [sphereCanonicalPotential] <;> push_cast <;> ring

theorem gaussianLogPotential_sphere_relation {t : ℝ} (ht : 0<t) (ht' : t≤1) :
    gaussianLogPotential t = (volume : Measure RealSpace4).toSphere.real univ *
      sphereCanonicalPotential t +
        2*(∫ x : RealSpace4, Real.log ‖x‖ * Real.exp (-‖x‖^2)) := by
  have hie := canonicalPotential_gaussian_sphere_integral t
  have he : (∫ x : RealSpace4, canonicalPotential t x * Real.exp (-‖x‖^2)) =
      (1/2:ℝ)*gaussianLogPotential t -
        ∫ x : RealSpace4, Real.log ‖x‖ * Real.exp (-‖x‖^2) := by
    unfold gaussianLogPotential
    rw [← integral_const_mul, ← integral_sub
      ((integrable_realGaussian_log_quadratic ht ht').const_mul (1/2:ℝ))
      (integrable_realGaussian_log_norm (0:Fin 4))]
    apply integral_congr_ae
    filter_upwards [real_euclidean_coordinate_ne_zero_ae (0:Fin 4)] with x hx
    have hq := (canonicalQuadratic_bounds ht ht' x hx).1
    have hn : ‖x‖^2 ≠ 0 := ne_of_gt (hq.trans_le (canonicalQuadratic_bounds ht ht' x hx).2.1)
    simp only [canonicalPotential,Real.log_div hq.ne' hn,Real.log_pow,Nat.cast_ofNat]
    ring
  linarith

/-- Uniform real sphere potential has its unique maximum at the balanced parameter. -/
theorem sphereCanonicalPotential_strict_balanced {t : ℝ} (ht : 1/2<t) (ht' : t≤1) :
    sphereCanonicalPotential t < sphereCanonicalPotential (1/2) := by
  have h := gaussianLogPotential_strict_balanced ht ht'
  rw [gaussianLogPotential_sphere_relation (by linarith) ht',
    gaussianLogPotential_sphere_relation (by norm_num : (0:ℝ)<1/2) (by norm_num)] at h
  have hmass : 0 < (volume : Measure RealSpace4).toSphere.real univ := by
    apply ENNReal.toReal_pos
    · exact (measure_univ_pos.mpr (volume : Measure RealSpace4).toSphere_ne_zero).ne'
    · exact measure_ne_top _ _
  nlinarith

end
end BapatRealExistence
