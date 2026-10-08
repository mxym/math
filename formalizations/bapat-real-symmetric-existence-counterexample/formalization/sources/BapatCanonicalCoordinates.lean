import BapatComplexBalanceCoordinates

set_option autoImplicit false

namespace BapatRealExistence
noncomputable section

/-- Two Householder reflections align an orthogonal pair, even when the second vector is zero. -/
theorem exists_real_axis_alignment (x y : RealSpace4) (hx : 0 < ‖x‖)
    (hxy : inner ℝ x y = 0) :
    ∃ R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4,
      R x = ‖x‖ • EuclideanSpace.single (0:Fin 4) 1 ∧
      R y = ‖y‖ • EuclideanSpace.single (1:Fin 4) 1 := by
  let e0 : RealSpace4 := EuclideanSpace.single (0:Fin 4) 1
  let e1 : RealSpace4 := EuclideanSpace.single (1:Fin 4) 1
  have he0 : ‖e0‖=1 := by simp [e0]
  have he1 : ‖e1‖=1 := by simp [e1]
  let E := (Submodule.span ℝ {x-‖x‖ • e0})ᗮ.reflection
  have hE : E x = ‖x‖ • e0 := Submodule.reflection_sub (by simp [norm_smul,he0])
  have hy0 : inner ℝ (E y) e0 = 0 := by
    have h := E.inner_map_map x y
    rw [hE,hxy,real_inner_smul_left] at h
    have hz := (mul_eq_zero.mp h).resolve_left hx.ne'
    rwa [real_inner_comm] at hz
  let F := (Submodule.span ℝ {E y-‖y‖ • e1})ᗮ.reflection
  have hF : F (E y) = ‖y‖ • e1 := Submodule.reflection_sub (by simp [norm_smul,he1])
  have hF0 : F e0 = e0 := by
    apply Submodule.reflection_mem_subspace_eq_self
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_left,hy0,real_inner_smul_left]
    simp [e0,e1,EuclideanSpace.inner_single_left]
  refine ⟨E.trans F,?_,?_⟩
  · change F (E x) = ‖x‖ • e0
    rw [hE,map_smul,hF0]
  · exact hF

def complexifyRealIsometry (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (z : EuclideanSpace ℂ (Fin 4)) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun i => ((R (complexRealPart4 z) i : ℝ) : ℂ) +
    Complex.I*((R (complexImagPart4 z) i : ℝ) : ℂ))

@[simp] theorem complexifyRealIsometry_re (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (z : EuclideanSpace ℂ (Fin 4)) :
    complexRealPart4 (complexifyRealIsometry R z) = R (complexRealPart4 z) := by
  ext i
  simp [complexRealPart4,complexifyRealIsometry]

@[simp] theorem complexifyRealIsometry_im (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (z : EuclideanSpace ℂ (Fin 4)) :
    complexImagPart4 (complexifyRealIsometry R z) = R (complexImagPart4 z) := by
  ext i
  simp [complexImagPart4,complexifyRealIsometry]

theorem complexifyRealIsometry_norm (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (z : EuclideanSpace ℂ (Fin 4)) : ‖complexifyRealIsometry R z‖ = ‖z‖ := by
  have h := complex_real_imag_norm_sq (complexifyRealIsometry R z)
  rw [complexifyRealIsometry_re,complexifyRealIsometry_im,R.norm_map,R.norm_map,
    ← complex_real_imag_norm_sq z] at h
  nlinarith [norm_nonneg (complexifyRealIsometry R z),norm_nonneg z]

theorem complexifyRealIsometry_symm_apply (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (z : EuclideanSpace ℂ (Fin 4)) :
    complexifyRealIsometry R.symm (complexifyRealIsometry R z) = z := by
  ext i
  simp [complexifyRealIsometry,complexRealPart4,complexImagPart4,Complex.ext_iff]

/-- Every complex unit vector admits actual real orthogonal canonical coordinates. -/
theorem exists_canonical_coordinates (z : ComplexUnitSphere4) :
    ∃ a : ℂ, ‖a‖=1 ∧ ∃ R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4,
      complexifyRealIsometry R (a • (z : EuclideanSpace ℂ (Fin 4))) =
        canonicalComplex4 (balanceParameter z) := by
  obtain ⟨a,ha,horth,hx,hy⟩ := exists_balanced_real_imag_parts z
  have ht := balanceParameter_mem z
  have hxpos : 0 < ‖complexRealPart4 (a • (z : EuclideanSpace ℂ (Fin 4)))‖ := by
    nlinarith [norm_nonneg (complexRealPart4 (a • (z : EuclideanSpace ℂ (Fin 4))))]
  obtain ⟨R,hRx,hRy⟩ := exists_real_axis_alignment _ _ hxpos horth
  have hxn : ‖complexRealPart4 (a • (z : EuclideanSpace ℂ (Fin 4)))‖ = Real.sqrt (balanceParameter z) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ balanceParameter z by linarith [ht.1]),
      Real.sqrt_nonneg (balanceParameter z)]
  have hyn : ‖complexImagPart4 (a • (z : EuclideanSpace ℂ (Fin 4)))‖ = Real.sqrt (1-balanceParameter z) := by
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr ht.2),Real.sqrt_nonneg (1-balanceParameter z),
      norm_nonneg (complexImagPart4 (a • (z : EuclideanSpace ℂ (Fin 4))))]
  refine ⟨a,ha,R,?_⟩
  unfold complexifyRealIsometry
  rw [hRx,hRy,hxn,hyn]
  ext i
  fin_cases i <;> simp [canonicalComplex4,EuclideanSpace.single,PiLp.single_apply]

end
end BapatRealExistence
