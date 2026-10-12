import BapatTruncatedPotential

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Filter
open BapatFiniteRank

namespace BapatRealExistence
noncomputable section

def unitCoefficientRows {n : ℕ} (v : Fin n → RealUnitSphere4) : Fin n → Fin 4 → ℝ :=
  fun i j => (v i : RealSpace4) j

theorem unitCoefficientRows_product_norm {n : ℕ} (v : Fin n → RealUnitSphere4)
    (z : ComplexUnitSphere4) :
    rowProductModulus (unitCoefficientRows v) z = ∏ i, ‖realComplexLinear (v i) z‖ := by
  simp [rowProductModulus,complexEval_formsProduct,unitCoefficientRows,realComplexLinear,norm_prod]

theorem orthogonal_orbit_measurePreserving (v : RealUnitSphere4) :
    MeasurePreserving (fun R => orthogonalSphereAction R v) orthogonalHaar
      (normalizedSphere (volume : Measure RealSpace4)) := by
  refine ⟨?_,orthogonal_orbit_map v⟩
  exact (orthogonalSphereAction_continuous.comp (continuous_id.prodMk continuous_const)).measurable

theorem orthogonal_orbit_log_integrable (v : RealUnitSphere4) (z : ComplexUnitSphere4) :
    Integrable (fun R => Real.log ‖realComplexLinear (orthogonalSphereAction R v) z‖) orthogonalHaar :=
  (orthogonal_orbit_measurePreserving v).integrable_comp_of_integrable
    (realComplexLinear_log_integrable z)

theorem orthogonal_orbit_log_integral (v : RealUnitSphere4) (z : ComplexUnitSphere4) :
    (∫ R, Real.log ‖realComplexLinear (orthogonalSphereAction R v) z‖ ∂orthogonalHaar) =
      sphereLogPotential z := by
  have hm := (orthogonal_orbit_measurePreserving v).measurable
  have hi := (realComplexLinear_log_integrable z).aestronglyMeasurable
  rw [← orthogonal_orbit_map v] at hi
  have he := integral_map hm.aemeasurable hi
  rw [orthogonal_orbit_map v] at he
  exact he.symm

def balancedSphere4 : ComplexUnitSphere4 := canonicalSphere4 (1/2) (by norm_num) (by norm_num)

theorem balancedSphere4_potential : sphereLogPotential balancedSphere4 = sphereCanonicalPotential (1/2) := by
  unfold sphereLogPotential balancedSphere4
  simp_rw [show (canonicalSphere4 (1/2) (by norm_num) (by norm_num) : EuclideanSpace ℂ (Fin 4)) =
    canonicalComplex4 (1/2) from rfl,realComplexLinear_canonical_log (t := (1/2:ℝ)) (by norm_num) (by norm_num)]
  rfl

def rotatedBalancedSphere4 (R : Orthogonal4) : ComplexUnitSphere4 :=
  ⟨complexifyRealIsometry (Unitary.linearIsometryEquiv R).symm balancedSphere4,
    by simp only [Metric.mem_sphere,dist_zero_right,complexifyRealIsometry_norm];
       exact canonicalComplex4_norm (by norm_num) (by norm_num)⟩

theorem rotatedBalanced_linear (R : Orthogonal4) (v : RealUnitSphere4) :
    realComplexLinear v (rotatedBalancedSphere4 R) =
      realComplexLinear (orthogonalSphereAction R v) balancedSphere4 :=
  (realComplexLinear_isometry_symm (Unitary.linearIsometryEquiv R) v balancedSphere4).symm

theorem unitRows_orbit_nonzero_ae {n : ℕ} (v : Fin n → RealUnitSphere4) :
    ∀ᵐ R ∂orthogonalHaar, ∀ i, realComplexLinear (orthogonalSphereAction R (v i)) balancedSphere4 ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  exact (orthogonal_orbit_measurePreserving (v i)).quasiMeasurePreserving.ae
    (realComplexLinear_ne_zero_ae balancedSphere4)

theorem unitRows_exists_positive {n : ℕ} (v : Fin n → RealUnitSphere4) :
    ∃ z : ComplexUnitSphere4, 0 < rowProductModulus (unitCoefficientRows v) z := by
  obtain ⟨R,hR⟩ := (unitRows_orbit_nonzero_ae v).exists
  refine ⟨rotatedBalancedSphere4 R,?_⟩
  rw [unitCoefficientRows_product_norm]
  apply Finset.prod_pos
  intro i hi
  rw [rotatedBalanced_linear]
  exact norm_pos_iff.mpr (hR i)

theorem unitRows_exists_positive_maximum {n : ℕ} (v : Fin n → RealUnitSphere4) :
    ∃ z : ComplexUnitSphere4, 0 < rowProductModulus (unitCoefficientRows v) z ∧
      ∀ w, rowProductModulus (unitCoefficientRows v) w ≤ rowProductModulus (unitCoefficientRows v) z := by
  obtain ⟨w,hw⟩ := unitRows_exists_positive v
  letI : Nonempty ComplexUnitSphere4 := ⟨w⟩
  obtain ⟨z,hz,hm⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (rowProductModulus_continuous (unitCoefficientRows v)).continuousOn
  exact ⟨z,hw.trans_le (hm (Set.mem_univ w)),fun w => hm (Set.mem_univ w)⟩

/-- The true finite product maximum is bounded below by its Haar logarithmic average. -/
theorem unitRows_maximum_log_lower {n : ℕ} (v : Fin n → RealUnitSphere4)
    (z : ComplexUnitSphere4) (hmax : ∀ w,
      rowProductModulus (unitCoefficientRows v) w ≤ rowProductModulus (unitCoefficientRows v) z) :
    (n:ℝ)*sphereCanonicalPotential (1/2) ≤ Real.log (rowProductModulus (unitCoefficientRows v) z) := by
  let S : Orthogonal4 → ℝ := fun R => ∑ i, Real.log ‖realComplexLinear (orthogonalSphereAction R (v i)) balancedSphere4‖
  have hi : Integrable S orthogonalHaar :=
    integrable_finsetSum _ (fun i _ => orthogonal_orbit_log_integrable (v i) balancedSphere4)
  have hbound : ∀ᵐ R ∂orthogonalHaar, S R ≤ Real.log (rowProductModulus (unitCoefficientRows v) z) := by
    filter_upwards [unitRows_orbit_nonzero_ae v] with R hR
    have hp : 0 < rowProductModulus (unitCoefficientRows v) (rotatedBalancedSphere4 R) := by
      rw [unitCoefficientRows_product_norm]
      apply Finset.prod_pos
      intro i hi
      rw [rotatedBalanced_linear]
      exact norm_pos_iff.mpr (hR i)
    have hlog : Real.log (rowProductModulus (unitCoefficientRows v) (rotatedBalancedSphere4 R)) = S R := by
      rw [unitCoefficientRows_product_norm,Real.log_prod]
      · simp only [rotatedBalanced_linear,S]
      · intro i hi
        rw [rotatedBalanced_linear]
        exact norm_ne_zero_iff.mpr (hR i)
    rw [← hlog]
    exact Real.log_le_log hp (hmax _)
  have h := integral_mono_ae hi (integrable_const _) hbound
  rw [integral_const] at h
  have he : (∫ R, S R ∂orthogonalHaar) = (n:ℝ)*sphereCanonicalPotential (1/2) := by
    rw [integral_finsetSum _ (fun i _ => orthogonal_orbit_log_integrable (v i) balancedSphere4)]
    simp only [orthogonal_orbit_log_integral,balancedSphere4_potential,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simpa only [he,probReal_univ,one_smul] using h

end
end BapatRealExistence
