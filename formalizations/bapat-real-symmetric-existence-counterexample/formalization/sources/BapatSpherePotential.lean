import BapatRealComplexLinear

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped Pointwise

namespace BapatRealExistence
noncomputable section

theorem real_sphere_coordinate_ne_zero_ae (i : Fin 4) :
    ∀ᵐ v : RealUnitSphere4 ∂normalizedSphere (volume : Measure RealSpace4),
      (v:RealSpace4) i ≠ 0 := by
  let s : Set RealUnitSphere4 := {v | (v:RealSpace4) i = 0}
  have hs : MeasurableSet s := by
    apply (isClosed_eq _ continuous_const).measurableSet
    fun_prop
  have hz : (volume : Measure RealSpace4) {x | x i=0} = 0 := by
    simpa only [ae_iff,not_not] using real_euclidean_coordinate_ne_zero_ae i
  have hcone : (volume : Measure RealSpace4) (Ioo (0:ℝ) 1 • ((↑) '' s)) = 0 := by
    apply measure_mono_null _ hz
    rintro x ⟨r,hr,v,⟨v,hv,rfl⟩,rfl⟩
    change r*(v:RealSpace4) i=0
    rw [show (v:RealSpace4) i=0 from hv,mul_zero]
  have hσ : normalizedSphere (volume : Measure RealSpace4) s = 0 := by
    rw [normalizedSphere,Measure.smul_apply,Measure.toSphere_apply' _ hs,hcone]
    simp
  simpa only [ae_iff,not_not] using hσ

theorem canonical_linear_ne_zero_ae {t : ℝ} (ht : 0<t) (ht' : t≤1) :
    ∀ᵐ v : RealUnitSphere4 ∂normalizedSphere (volume : Measure RealSpace4),
      realComplexLinear v (canonicalComplex4 t) ≠ 0 := by
  filter_upwards [real_sphere_coordinate_ne_zero_ae (0:Fin 4)] with v hv
  have hq := (canonicalQuadratic_bounds ht ht' v hv).1
  rw [← realComplexLinear_canonical_norm_sq ht.le ht'] at hq
  intro h
  simp [h] at hq

/-- Phase and simultaneous real orthogonal changes preserve every individual modulus. -/
theorem canonical_linear_modulus_transport (z : ComplexUnitSphere4) (a : ℂ) (ha : ‖a‖=1)
    (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (hR : complexifyRealIsometry R (a • (z:EuclideanSpace ℂ (Fin 4))) =
      canonicalComplex4 (balanceParameter z)) (v : RealSpace4) :
    ‖realComplexLinear (R v) (canonicalComplex4 (balanceParameter z))‖ =
      ‖realComplexLinear v z‖ := by
  rw [← hR,realComplexLinear_isometry,realComplexLinear_smul,norm_mul,ha,one_mul]

theorem realComplexLinear_ne_zero_ae (z : ComplexUnitSphere4) :
    ∀ᵐ v : RealUnitSphere4 ∂normalizedSphere (volume : Measure RealSpace4),
      realComplexLinear v z ≠ 0 := by
  obtain ⟨a,ha,R,hR⟩ := exists_canonical_coordinates z
  have ht := balanceParameter_mem z
  have hcan := canonical_linear_ne_zero_ae (show 0<balanceParameter z by linarith [ht.1]) ht.2
  have h := (measurePreserving_normalizedSphere R).quasiMeasurePreserving.ae hcan
  filter_upwards [h] with v hv
  have hm := canonical_linear_modulus_transport z a ha R hR v
  intro hz
  have hn : ‖realComplexLinear (R (v:RealSpace4)) (canonicalComplex4 (balanceParameter z))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hv
  exact hn (by rw [hm,hz,norm_zero])

theorem realComplexLinear_log_integrable (z : ComplexUnitSphere4) :
    Integrable (fun v : RealUnitSphere4 => Real.log ‖realComplexLinear v z‖)
      (normalizedSphere (volume : Measure RealSpace4)) := by
  obtain ⟨a,ha,R,hR⟩ := exists_canonical_coordinates z
  have ht := balanceParameter_mem z
  have hcan : Integrable (fun v : RealUnitSphere4 =>
      Real.log ‖realComplexLinear v (canonicalComplex4 (balanceParameter z))‖)
      (normalizedSphere (volume : Measure RealSpace4)) := by
    simp_rw [realComplexLinear_canonical_log (show 0≤balanceParameter z by linarith [ht.1]) ht.2]
    exact canonicalPotential_sphere_integrable (by linarith [ht.1]) ht.2
  have h := (measurePreserving_normalizedSphere R).integrable_comp_of_integrable hcan
  convert h using 1
  ext v
  rw [Function.comp_def]
  exact congrArg Real.log (canonical_linear_modulus_transport z a ha R hR v).symm

def sphereLogPotential (z : ComplexUnitSphere4) : ℝ :=
  ∫ v : RealUnitSphere4, Real.log ‖realComplexLinear v z‖
    ∂normalizedSphere (volume : Measure RealSpace4)

theorem sphereLogPotential_canonical (z : ComplexUnitSphere4) :
    sphereLogPotential z = sphereCanonicalPotential (balanceParameter z) := by
  obtain ⟨a,ha,R,hR⟩ := exists_canonical_coordinates z
  have ht := balanceParameter_mem z
  calc
    _ = ∫ v : RealUnitSphere4, Real.log ‖realComplexLinear (R v)
          (canonicalComplex4 (balanceParameter z))‖
          ∂normalizedSphere (volume : Measure RealSpace4) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v =>
        congrArg Real.log (canonical_linear_modulus_transport z a ha R hR v).symm)
    _ = ∫ v : RealUnitSphere4, Real.log ‖realComplexLinear v
          (canonicalComplex4 (balanceParameter z))‖
          ∂normalizedSphere (volume : Measure RealSpace4) :=
      (measurePreserving_normalizedSphere R).integral_comp
        (unitSphereHomeomorph R).measurableEmbedding
        (fun v : RealUnitSphere4 => Real.log ‖realComplexLinear v
          (canonicalComplex4 (balanceParameter z))‖)
    _ = _ := by
      simp_rw [realComplexLinear_canonical_log (show 0≤balanceParameter z by linarith [ht.1]) ht.2]
      rfl

theorem sphereLogPotential_unique_balanced (z : ComplexUnitSphere4) :
    sphereLogPotential z ≤ sphereCanonicalPotential (1/2) ∧
      (sphereLogPotential z = sphereCanonicalPotential (1/2) ↔ balanceParameter z = 1/2) := by
  rw [sphereLogPotential_canonical]
  have ht := balanceParameter_mem z
  rcases eq_or_lt_of_le ht.1 with he | hl
  · rw [← he]
    exact ⟨le_rfl,by simp⟩
  · have h := sphereCanonicalPotential_strict_balanced hl ht.2
    exact ⟨h.le,⟨fun he => False.elim (h.ne he),fun he => False.elim (hl.ne he.symm)⟩⟩

end
end BapatRealExistence
