import CofactorFiniteBinaryNorm

/-! The factor two for signed real coordinates in the binary-vector bound. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem binaryNormConstant_nonneg (n : ℕ) : 0 ≤ binaryNormConstant n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem real_binary_norm_bound {n : ℕ} (u : Fin n → E) (x : Fin n → ℝ)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖ ≤ Real.sqrt s.card) :
    ‖∑ i, x i • u i‖^2 ≤ 2 * binaryNormConstant n * ∑ i, x i ^ 2 := by
  classical
  let xp : Fin n → ℝ := fun i => max (x i) 0
  let xm : Fin n → ℝ := fun i => max (-x i) 0
  have hp := nonneg_binary_norm_bound u xp (fun i => le_max_right _ _) hu
  have hm := nonneg_binary_norm_bound u xm (fun i => le_max_right _ _) hu
  have hx : ∀ i, x i = xp i - xm i := by
    intro i
    dsimp [xp,xm]
    by_cases h : 0 ≤ x i
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · have hle : x i ≤ 0 := le_of_not_ge h
      rw [max_eq_right hle,max_eq_left (neg_nonneg.mpr hle)]
      ring
  have hs : ∑ i, x i • u i = (∑ i, xp i • u i) - ∑ i, xm i • u i := by
    simp_rw [hx,sub_smul,Finset.sum_sub_distrib]
  have hsq : (∑ i, xp i ^ 2) + (∑ i, xm i ^ 2) = ∑ i, x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [xp,xm]
    by_cases h : 0 ≤ x i
    · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
      ring
    · have hle : x i ≤ 0 := le_of_not_ge h
      rw [max_eq_right hle,max_eq_left (neg_nonneg.mpr hle)]
      ring
  have ht : ‖∑ i, x i • u i‖ ≤ ‖∑ i, xp i • u i‖ + ‖∑ i, xm i • u i‖ := by
    rw [hs]
    exact norm_sub_le _ _
  have hsquare : ‖∑ i, x i • u i‖^2 ≤
      (‖∑ i, xp i • u i‖ + ‖∑ i, xm i • u i‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
  have hdiff := sq_nonneg (‖∑ i, xp i • u i‖ - ‖∑ i, xm i • u i‖)
  rw [← hsq]
  nlinarith

theorem real_binary_norm_harmonic_bound {n : ℕ} (u : Fin n → E) (x : Fin n → ℝ)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖ ≤ Real.sqrt s.card) :
    ‖∑ i, x i • u i‖^2 ≤ (2 + (harmonic (n-1) : ℝ)/2) * ∑ i, x i ^ 2 := by
  have h := real_binary_norm_bound u x hu
  have hc := binaryNormConstant_le_harmonic n
  have hn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hc hn]

end
end CofactorSpectral
