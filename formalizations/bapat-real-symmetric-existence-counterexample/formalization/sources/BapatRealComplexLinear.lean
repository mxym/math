import BapatCanonicalCoordinates

set_option autoImplicit false
open BapatFiniteRank

namespace BapatRealExistence
noncomputable section

def realComplexLinear (v : RealSpace4) (z : EuclideanSpace ℂ (Fin 4)) : ℂ :=
  ∑ i, (v i : ℂ)*z i

@[fun_prop] theorem realComplexLinear_continuous :
    Continuous (fun p : RealSpace4 × EuclideanSpace ℂ (Fin 4) => realComplexLinear p.1 p.2) := by
  unfold realComplexLinear
  fun_prop

theorem realComplexLinear_eq_eval (v : RealSpace4) (z : EuclideanSpace ℂ (Fin 4)) :
    realComplexLinear v z = complexEval (linearForm (fun i => v i)) z :=
  (complexEval_linearForm _ _).symm

theorem realComplexLinear_smul (v : RealSpace4) (z : EuclideanSpace ℂ (Fin 4)) (a : ℂ) :
    realComplexLinear v (a • z) = a*realComplexLinear v z := by
  simp only [realComplexLinear,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem realComplexLinear_eq_inner (v : RealSpace4) (z : EuclideanSpace ℂ (Fin 4)) :
    realComplexLinear v z = ((inner ℝ v (complexRealPart4 z) : ℝ) : ℂ) +
      Complex.I*((inner ℝ v (complexImagPart4 z) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [realComplexLinear,PiLp.inner_apply,RCLike.inner_apply,complexRealPart4,complexImagPart4,
      mul_comm]

theorem realComplexLinear_isometry (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (v : RealSpace4) (z : EuclideanSpace ℂ (Fin 4)) :
    realComplexLinear (R v) (complexifyRealIsometry R z) = realComplexLinear v z := by
  rw [realComplexLinear_eq_inner,realComplexLinear_eq_inner,
    complexifyRealIsometry_re,complexifyRealIsometry_im,R.inner_map_map,R.inner_map_map]

theorem realComplexLinear_isometry_symm (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (v : RealSpace4) (z : EuclideanSpace ℂ (Fin 4)) :
    realComplexLinear (R v) z = realComplexLinear v (complexifyRealIsometry R.symm z) := by
  have he : complexifyRealIsometry R (complexifyRealIsometry R.symm z) = z := by
    simpa only [LinearIsometryEquiv.symm_symm] using complexifyRealIsometry_symm_apply R.symm z
  simpa only [he] using realComplexLinear_isometry R v (complexifyRealIsometry R.symm z)

theorem realComplexLinear_canonical_norm_sq {t : ℝ} (ht : 0≤t) (ht' : t≤1) (v : RealSpace4) :
    ‖realComplexLinear v (canonicalComplex4 t)‖^2 = canonicalQuadratic t v := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [realComplexLinear,canonicalComplex4,Fin.sum_univ_succ,Complex.normSq_apply,
    mul_pow,Real.sq_sqrt ht,Real.sq_sqrt (sub_nonneg.mpr ht'),canonicalQuadratic]
  ring_nf
  rw [Real.sq_sqrt ht, Real.sq_sqrt (sub_nonneg.mpr ht')]
  ring

theorem realComplexLinear_canonical_log {t : ℝ} (ht : 0≤t) (ht' : t≤1) (v : RealUnitSphere4) :
    Real.log ‖realComplexLinear v (canonicalComplex4 t)‖ = canonicalPotential t v := by
  rw [canonicalPotential_on_sphere,← realComplexLinear_canonical_norm_sq ht ht',Real.log_pow]
  norm_num
  <;> ring

end
end BapatRealExistence
