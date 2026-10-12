import GaussianRegularValue

/-! A centered trace-one equidistant score family has precisely the regular
simplex covariance. The proof is finite inner-product algebra in any ambient
dimension. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma sum_squared_distances_centered (v : Fin k → Space d)
    (hz : ∑ i, v i = 0) (i : Fin k) :
    (∑ j, ‖v i-v j‖^2) = (k : ℝ)*‖v i‖^2 + ∑ j, ‖v j‖^2 := by
  have he (j : Fin k) : ‖v i-v j‖^2 = ‖v i‖^2 + ‖v j‖^2 - 2*⟪v i,v j⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq]
    rw [real_inner_comm (v j) (v i)]
    ring
  simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    ← inner_sum,hz,inner_zero_right]
  simp

theorem equidistant_centered_gram_regular (hk : 2 ≤ k) (v : Fin k → Space d)
    (hz : ∑ i, v i = 0) (htrace : ∑ i, ‖v i‖^2 = 1)
    (a : ℝ) (ha : ∀ i j, i ≠ j → ‖v i-v j‖^2 = a) :
    scoreGram v = regularCovariance k := by
  classical
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hk1 : (k : ℝ)-1 ≠ 0 := by
    have hp : (2:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hd (i : Fin k) : (∑ j, ‖v i-v j‖^2) = ((k:ℝ)-1)*a := by
    have ht (j : Fin k) : ‖v i-v j‖^2 = if j = i then 0 else a := by
      by_cases he : j = i
      · simp [he]
      · simp only [he,ite_false]
        exact ha i j (Ne.symm he)
    simp_rw [ht]
    have ht' (j : Fin k) : (if j = i then 0 else a) = a - (if j = i then a else 0) := by
      by_cases hj : j = i <;> simp [hj]
    simp_rw [ht',Finset.sum_sub_distrib]
    simp
    ring
  have he (i : Fin k) : (k:ℝ)*‖v i‖^2 + 1 = ((k:ℝ)-1)*a := by
    rw [← hd i,sum_squared_distances_centered v hz,htrace]
  have hnorm (i j : Fin k) : ‖v i‖^2 = ‖v j‖^2 := by
    have hh : (k:ℝ)*(‖v i‖^2-‖v j‖^2) = 0 := by linarith [he i,he j]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hk0)
  have hni (i : Fin k) : ‖v i‖^2 = (k:ℝ)⁻¹ := by
    have hs := htrace
    simp_rw [hnorm _ i] at hs
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    apply (mul_left_cancel₀ hk0)
    rw [hs,mul_inv_cancel₀ hk0]
  have haa : a = 2/((k:ℝ)-1) := by
    have hh := he (0 : Fin k)
    rw [hni,mul_inv_cancel₀ hk0] at hh
    apply (eq_div_iff hk1).mpr
    linarith
  ext i j
  rw [regularCovariance_apply]
  have hcast : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k),Nat.cast_one]
  rw [hcast]
  by_cases hij : i = j
  · subst j
    simp only [scoreGram,real_inner_self_eq_norm_sq,hni,ite_true]
    field_simp
  · have hh := ha i j hij
    rw [haa,← real_inner_self_eq_norm_sq] at hh
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq,hni] at hh
    rw [real_inner_comm (v j) (v i)] at hh
    simp only [scoreGram,hij,ite_false,zero_sub]
    rw [real_inner_comm (v j) (v i)]
    field_simp at hh ⊢
    nlinarith

end GaussianMeasureBridge
