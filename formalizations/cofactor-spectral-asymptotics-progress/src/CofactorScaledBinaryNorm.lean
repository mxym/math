import CofactorComplexBinaryNorm

/-! Homogeneity of the proved binary norm estimates. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rescaled_binary_hypothesis {n : ℕ} (u : Fin n → E) (κ : ℝ) (hκ : 0 < κ)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖^2 ≤ κ^2 * s.card) :
    ∀ s : Finset (Fin n), ‖∑ i ∈ s, κ⁻¹ • u i‖ ≤ Real.sqrt s.card := by
  intro s
  rw [← Finset.smul_sum,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hκ)]
  have hnorm : ‖∑ i ∈ s, u i‖ ≤ κ * Real.sqrt s.card := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)
    have he : κ^2 * (s.card : ℝ) = (κ * Real.sqrt s.card)^2 := by
      calc
        _ = κ^2 * (Real.sqrt s.card)^2 := congrArg (fun r : ℝ => κ^2 * r) hs.symm
        _ = _ := by ring
    have h : ‖∑ i ∈ s, u i‖^2 ≤ (κ * Real.sqrt s.card)^2 := by
      rw [← he]
      exact hu s
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hκ.le (Real.sqrt_nonneg _))).mp h
  calc
    _ ≤ κ⁻¹ * (κ * Real.sqrt s.card) :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hκ.le)
    _ = _ := by field_simp

theorem real_sum_rescale_norm_sq {n : ℕ} (u : Fin n → E) (x : Fin n → ℝ)
    (κ : ℝ) (hκ : 0 < κ) :
    κ^2 * ‖∑ i, x i • (κ⁻¹ • u i)‖^2 = ‖∑ i, x i • u i‖^2 := by
  have hs : (∑ i, x i • (κ⁻¹ • u i)) = κ⁻¹ • ∑ i, x i • u i := by
    simp_rw [smul_comm (x _) κ⁻¹,Finset.smul_sum]
  rw [hs,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hκ)]
  field_simp

theorem real_scaled_binary_norm_bound {n : ℕ} (u : Fin n → E) (x : Fin n → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖^2 ≤ κ^2 * s.card) :
    ‖∑ i, x i • u i‖^2 ≤ 2 * binaryNormConstant n * κ^2 * ∑ i, x i ^ 2 := by
  have h := real_binary_norm_bound (fun i => κ⁻¹ • u i) x
    (rescaled_binary_hypothesis u κ hκ hu)
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg κ)
  rw [real_sum_rescale_norm_sq u x κ hκ] at hm
  nlinarith

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem complex_sum_rescale_norm_sq {n : ℕ} (u : Fin n → E) (w : Fin n → ℂ)
    (κ : ℝ) (hκ : 0 < κ) :
    κ^2 * ‖∑ i, w i • (κ⁻¹ • u i)‖^2 = ‖∑ i, w i • u i‖^2 := by
  have hs : (∑ i, w i • (κ⁻¹ • u i)) = κ⁻¹ • ∑ i, w i • u i := by
    simp_rw [smul_comm (w _) κ⁻¹,Finset.smul_sum]
  rw [hs,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hκ)]
  field_simp

theorem complex_scaled_binary_norm_bound {n : ℕ} (u : Fin n → E) (w : Fin n → ℂ)
    (κ : ℝ) (hκ : 0 < κ)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖^2 ≤ κ^2 * s.card) :
    ‖∑ i, w i • u i‖^2 ≤ 4 * binaryNormConstant n * κ^2 *
      ∑ i, Complex.normSq (w i) := by
  have h := complex_binary_norm_bound (fun i => κ⁻¹ • u i) w
    (rescaled_binary_hypothesis u κ hκ hu)
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg κ)
  rw [complex_sum_rescale_norm_sq u w κ hκ] at hm
  nlinarith

end
end CofactorSpectral
