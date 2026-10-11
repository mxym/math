import APPTReview.UniformPurityUpper

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The explicit finite upper estimate in conventional local-dimension notation. -/
theorem density_appt_dimension_only_upper {m n : ℕ} (hm : 8≤m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) ≤
      ((m:ℝ)/((m:ℝ)-7))^2*max 8 (4+(n:ℝ)/m) := by
  obtain ⟨h,rfl⟩ : ∃ h, m=h+1 := ⟨m-1,by omega⟩
  have hu := density_appt_explicit_uniform_upper (by omega : 7≤h) hmn hρ happt
  dsimp only at hu
  have he : (((h+1:ℕ):ℝ)*n)/((h:ℝ)+1)^2=(n:ℝ)/((h:ℝ)+1) := by
    have hz : (h:ℝ)+1≠0 := by positivity
    push_cast
    field_simp
    <;> ring
  rw [he] at hu
  have hd : (h:ℝ)+1-7=(h:ℝ)-6 := by ring
  simpa only [Nat.cast_add,Nat.cast_one,hd] using hu

/-- An explicit modulus for the rational error factor; all constants are exact. -/
theorem dimension_error_factor (m ε : ℝ) (hm : 8≤m) (hε : 0<ε)
    (hsize : 63/ε+7≤m) : (m/(m-7))^2≤1+ε := by
  have ht : 1≤m-7 := by linarith
  have htp : 0<m-7 := by linarith
  have he : 63≤(m-7)*ε := (div_le_iff₀ hε).mp (by linarith : 63/ε≤m-7)
  have hex := mul_le_mul_of_nonneg_right he htp.le
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos htp)).2
  nlinarith

/-- Uniform upper asymptotic for every actual APPT state, allowing n and the state
to vary arbitrarily with m. This is the upper half only, not an attained maximum. -/
theorem appt_uniform_asymptotic_upper (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, ∀ (m n : ℕ), M≤m → m≤n →
      ∀ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A → APPT.Quantum.AbsolutelyPPT A →
      ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) ≤
        (1+ε)*max 8 (4+(n:ℝ)/m) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max (8:ℝ) (63/ε+7))
  refine ⟨M, ?_⟩
  intro m n hm hmn A hρ happt
  have hmR : (M:ℝ)≤m := by exact_mod_cast hm
  have h8 : (8:ℝ)≤m := (le_max_left _ _).trans (hM.le.trans hmR)
  have hsize : 63/ε+7≤(m:ℝ) := (le_max_right _ _).trans (hM.le.trans hmR)
  have hu := density_appt_dimension_only_upper (by exact_mod_cast h8) hmn hρ happt
  have he := dimension_error_factor (m:ℝ) ε h8 hε hsize
  have hK : 0≤max (8:ℝ) (4+(n:ℝ)/m) := le_trans (by norm_num) (le_max_left _ _)
  exact hu.trans (mul_le_mul_of_nonneg_right he hK)

end APPTReview
