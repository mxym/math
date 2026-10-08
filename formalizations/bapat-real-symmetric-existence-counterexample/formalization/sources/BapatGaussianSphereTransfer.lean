import BapatRealGaussianPotential

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric

namespace BapatRealExistence
noncomputable section

/-- Gaussian integrability of a degree-zero function implies genuine sphere integrability. -/
theorem sphere_integrable_of_homogeneous_gaussian (h : RealSpace4 → ℝ)
    (hh : ∀ r : ℝ, 0 < r → ∀ x, h (r • x) = h x)
    (hg : Integrable (fun x : RealSpace4 => h x * Real.exp (-‖x‖^2))) :
    Integrable (fun x : RealUnitSphere4 => h x) (normalizedSphere (volume : Measure RealSpace4)) := by
  let μ := (volume : Measure RealSpace4)
  let ν := volumeIoiPow (Module.finrank ℝ RealSpace4-1)
  let g : RealUnitSphere4 × Ioi (0:ℝ) → ℝ :=
    fun p => h p.1 * Real.exp (-(p.2:ℝ)^2)
  have hsub : Integrable (fun x : ({(0)}ᶜ : Set RealSpace4) =>
      h x * Real.exp (-‖(x:RealSpace4)‖^2)) (μ.comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0:RealSpace4)).compl).mp hg.integrableOn
  have hprod : Integrable g (μ.toSphere.prod ν) := by
    rw [← μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (Homeomorph.measurableEmbedding _)]
    apply hsub.congr
    apply Filter.Eventually.of_forall
    intro x
    have hx : 0 < ‖(x:RealSpace4)‖ := norm_pos_iff.mpr x.property
    simp only [Function.comp_def,g,homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe]
    rw [hh _ (inv_pos.mpr hx)]
  have hν : ν ≠ 0 := by
    intro he
    have hv := congrArg (fun m : Measure (Ioi (0:ℝ)) => m (Iio ⟨1,by norm_num⟩)) he
    norm_num [ν,RealSpace4,volumeIoiPow_apply_Iio] at hv
  letI : NeZero ν := ⟨hν⟩
  obtain ⟨r,hr⟩ := hprod.prod_left_ae.exists
  dsimp only [g] at hr
  have hi : Integrable (fun x : RealUnitSphere4 => h x) μ.toSphere :=
    (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero (-(r:ℝ)^2))) _).mp hr
  apply hi.smul_measure
  apply ENNReal.inv_ne_top.mpr
  intro he
  exact μ.toSphere_ne_zero (measure_univ_eq_zero.mp he)

def canonicalPotential (t : ℝ) (x : RealSpace4) : ℝ :=
  (1/2:ℝ)*Real.log (canonicalQuadratic t x / ‖x‖^2)

theorem canonicalQuadratic_smul (t r : ℝ) (x : RealSpace4) :
    canonicalQuadratic t (r • x) = r^2 * canonicalQuadratic t x := by
  simp only [canonicalQuadratic,PiLp.smul_apply,smul_eq_mul]
  ring

theorem canonicalPotential_smul (t r : ℝ) (hr : 0 < r) (x : RealSpace4) :
    canonicalPotential t (r • x) = canonicalPotential t x := by
  simp only [canonicalPotential,canonicalQuadratic_smul,norm_smul,
    Real.norm_eq_abs,abs_of_pos hr,mul_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hr.ne')]

theorem canonicalPotential_gaussian_integrable {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    Integrable (fun x : RealSpace4 => canonicalPotential t x * Real.exp (-‖x‖^2)) := by
  have hi := ((integrable_realGaussian_log_quadratic ht ht').const_mul (1/2:ℝ)).sub
    (integrable_realGaussian_log_norm (0:Fin 4))
  apply hi.congr
  filter_upwards [real_euclidean_coordinate_ne_zero_ae (0:Fin 4)] with x hx
  have hq := (canonicalQuadratic_bounds ht ht' x hx).1
  have hn : ‖x‖^2 ≠ 0 := ne_of_gt (hq.trans_le (canonicalQuadratic_bounds ht ht' x hx).2.1)
  simp only [Pi.sub_apply,canonicalPotential,Real.log_div hq.ne' hn,Real.log_pow,Nat.cast_ofNat]
  ring

theorem canonicalPotential_sphere_integrable {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    Integrable (fun x : RealUnitSphere4 => canonicalPotential t x)
      (normalizedSphere (volume : Measure RealSpace4)) :=
  sphere_integrable_of_homogeneous_gaussian _ (canonicalPotential_smul t)
    (canonicalPotential_gaussian_integrable ht ht')

theorem canonicalPotential_on_sphere (t : ℝ) (x : RealUnitSphere4) :
    canonicalPotential t x = (1/2:ℝ)*Real.log (canonicalQuadratic t x) := by
  have hx : ‖(x:RealSpace4)‖ = 1 := by simpa using x.property
  simp only [canonicalPotential,hx,one_pow,div_one]

end
end BapatRealExistence
