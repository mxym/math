import CofactorEigenvalueUpper

/-! The complete upper half of the sharp logarithmic theorem. -/
set_option autoImplicit false
open scoped BigOperators
open Filter
namespace CofactorSpectral
noncomputable section

theorem harmonic_predecessor_le_log (n : ℕ) :
    (harmonic (n-1) : ℝ) ≤ 1 + Real.log n := by
  have hmono : (harmonic (n-1) : ℝ) ≤ (harmonic n : ℝ) := by
    simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le n 1))
    intro j _ _
    positivity
  exact hmono.trans (harmonic_le_one_add_log n)

theorem complex_variational_log_upper (n : ℕ)
    (P : Matrix (Fin n) (Fin n) ℂ → Prop) (hP : ∀ A, P A → psdAdmissible A) :
    sSup (complexRayleighValues n P) ≤ 5 + Real.log n := by
  have h := complex_variational_sSup_upper n P hP
  have hl := harmonic_predecessor_le_log n
  linarith

theorem real_variational_log_upper (n : ℕ)
    (P : Matrix (Fin n) (Fin n) ℂ → Prop) (hP : ∀ A, P A → psdAdmissible A) :
    sSup (realRayleighValues n P) ≤ 5/2 + Real.log n / 2 := by
  have h := real_variational_sSup_upper n P hP
  have hl := harmonic_predecessor_le_log n
  linarith

theorem complex_variational_eventual_log_upper
    (P : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ → Prop)
    (hP : ∀ n A, P n A → psdAdmissible A) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      sSup (complexRayleighValues n (P n)) / Real.log n ≤ 1 + ε := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, max 1 (5/ε) ≤ Real.log n :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,?_⟩
  intro n hn
  have hlog : 0 < Real.log n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans (hN n hn))
  have hlarge : 5/ε ≤ Real.log n := (le_max_right _ _).trans (hN n hn)
  have herr : 5 ≤ ε * Real.log n := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith
  rw [div_le_iff₀ hlog]
  have h := complex_variational_log_upper n (P n) (hP n)
  nlinarith

theorem real_variational_eventual_log_upper
    (P : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ → Prop)
    (hP : ∀ n A, P n A → psdAdmissible A) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      sSup (realRayleighValues n (P n)) / Real.log n ≤ 1/2 + ε := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, max 1 ((5/2)/ε) ≤ Real.log n :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,?_⟩
  intro n hn
  have hlog : 0 < Real.log n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans (hN n hn))
  have hlarge : (5/2)/ε ≤ Real.log n := (le_max_right _ _).trans (hN n hn)
  have herr : 5/2 ≤ ε * Real.log n := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith
  rw [div_le_iff₀ hlog]
  have h := real_variational_log_upper n (P n) (hP n)
  nlinarith

end
end CofactorSpectral
