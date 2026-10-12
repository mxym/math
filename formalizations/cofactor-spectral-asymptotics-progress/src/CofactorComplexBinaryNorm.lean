import CofactorSignedBinaryNorm

/-! The factor four for arbitrary complex coordinates in the binary-vector bound. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem complex_binary_norm_bound {n : ℕ} (u : Fin n → E) (w : Fin n → ℂ)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖ ≤ Real.sqrt s.card) :
    ‖∑ i, w i • u i‖^2 ≤ 4 * binaryNormConstant n * ∑ i, Complex.normSq (w i) := by
  have hr := real_binary_norm_bound u (fun i => (w i).re) hu
  have hi := real_binary_norm_bound u (fun i => (w i).im) hu
  have hw : ∑ i, w i • u i =
      (∑ i, (w i).re • u i) + Complex.I • ∑ i, (w i).im • u i := by
    rw [Finset.smul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => rw [← Complex.re_add_im (w i)]
    simp only [add_smul,mul_smul]
    congr 1
    · exact IsScalarTower.algebraMap_smul ℂ (w i).re (u i)
    · calc
        _ = (w i).im • (Complex.I • u i) :=
          IsScalarTower.algebraMap_smul ℂ (w i).im (Complex.I • u i)
        _ = _ := smul_comm _ _ _
  have hn : ‖∑ i, w i • u i‖ ≤
      ‖∑ i, (w i).re • u i‖ + ‖∑ i, (w i).im • u i‖ := by
    rw [hw]
    simpa only [norm_smul,Complex.norm_I,one_mul] using
      norm_add_le (∑ i, (w i).re • u i) (Complex.I • ∑ i, (w i).im • u i)
  have hsq : ‖∑ i, w i • u i‖^2 ≤
      (‖∑ i, (w i).re • u i‖ + ‖∑ i, (w i).im • u i‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hdiff := sq_nonneg (‖∑ i, (w i).re • u i‖ - ‖∑ i, (w i).im • u i‖)
  have hsum : (∑ i, (w i).re^2) + (∑ i, (w i).im^2) =
      ∑ i, Complex.normSq (w i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Complex.normSq_apply,pow_two]
  rw [← hsum]
  nlinarith

theorem complex_binary_norm_harmonic_bound {n : ℕ} (u : Fin n → E) (w : Fin n → ℂ)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖ ≤ Real.sqrt s.card) :
    ‖∑ i, w i • u i‖^2 ≤ (4 + (harmonic (n-1) : ℝ)) *
      ∑ i, Complex.normSq (w i) := by
  have h := complex_binary_norm_bound u w hu
  have hc := binaryNormConstant_le_harmonic n
  have hn : 0 ≤ ∑ i, Complex.normSq (w i) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hc hn]

end
end CofactorSpectral
