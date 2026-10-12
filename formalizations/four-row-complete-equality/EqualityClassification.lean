import ExtremizerValues
open scoped BigOperators ComplexConjugate
namespace FourRowTradeoff
noncomputable section

/-- Zero product is exactly an actual zero row, including all degenerate cases. -/
theorem rowProduct_eq_zero_iff (A : Mat) :
    rowProduct A = 0 ↔ ∃ i, ∀ j, A i j = 0 := by
  classical
  rw [rowProduct, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, (rowSq_eq_zero_iff _).mp ?_⟩
    rw [← rowNorm_sq, hi]; norm_num
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [rowNorm, (rowSq_eq_zero_iff _).mpr hi, Real.sqrt_zero]

theorem nonzero_rows_of_rowProduct_ne_zero (A : Mat) (h : rowProduct A ≠ 0) :
    NonzeroRows A := by
  classical
  intro i
  by_contra hi
  have hz : ∀ j, A i j = 0 := by simpa only [not_exists, not_not] using hi
  exact h ((rowProduct_eq_zero_iff A).mpr ⟨i,hz⟩)

/-- The complete critical equality theorem. -/
theorem critical_equality_iff (A : Mat) (hn : NonzeroRows A) :
    ‖A.permanent‖ + (1/2 : ℝ)*‖A.det‖ = (3/2 : ℝ)*rowProduct A ↔
      IsFlatRankOne A ∨ IsMonomial A := by
  constructor
  · exact critical_equality_only A hn
  · rintro (hf | hm)
    · obtain ⟨hp,hd⟩ := flat_values A hf
      simp only [hp,hd,norm_zero,mul_zero,add_zero]
    · obtain ⟨hp,hd⟩ := monomial_values A hm
      rw [hp,hd]; ring

theorem critical_matrix_bound (A : Mat) :
    ‖A.permanent‖ + (1/2 : ℝ)*‖A.det‖ ≤ (3/2 : ℝ)*rowProduct A := by
  have h := matrix_tradeoff A (1/2) (by norm_num)
  norm_num [sharpConstant] at h
  exact h

theorem subcritical_equality_only (A : Mat) (hn : NonzeroRows A)
    (c : ℝ) (hc : c < 1/2)
    (he : ‖A.permanent‖ + c*‖A.det‖ = sharpConstant c*rowProduct A) :
    IsFlatRankOne A := by
  have hM : sharpConstant c = (3/2 : ℝ) := max_eq_left (by linarith)
  rw [hM] at he
  have hb := critical_matrix_bound A
  have hpos : 0 < (1/2 : ℝ)-c := by linarith
  have hD : ‖A.det‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    have hm : ((1/2 : ℝ)-c)*‖A.det‖ ≤ ((1/2 : ℝ)-c)*0 := by nlinarith
    exact le_of_mul_le_mul_left hm hpos
  have hce : ‖A.permanent‖ + (1/2 : ℝ)*‖A.det‖ = (3/2 : ℝ)*rowProduct A := by
    rw [hD] at he ⊢; simpa using he
  rcases critical_equality_only A hn hce with hf | hm
  · exact hf
  · have hv := (monomial_values A hm).2
    have hp := rowProduct_pos A hn
    exfalso; linarith

theorem supercritical_equality_only (A : Mat) (hn : NonzeroRows A)
    (c : ℝ) (hc : 1/2 < c)
    (he : ‖A.permanent‖ + c*‖A.det‖ = sharpConstant c*rowProduct A) :
    IsMonomial A := by
  have hM : sharpConstant c = 1+c := max_eq_right (by linarith)
  rw [hM] at he
  have hb := critical_matrix_bound A
  have hd := det_norm_le_rowProduct A
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ c-(1/2 : ℝ) by linarith)
  have hce : ‖A.permanent‖ + (1/2 : ℝ)*‖A.det‖ = (3/2 : ℝ)*rowProduct A := by
    apply le_antisymm hb
    nlinarith
  rcases critical_equality_only A hn hce with hf | hm
  · obtain ⟨hp,hdet⟩ := flat_values A hf
    rw [hdet, norm_zero, mul_zero, add_zero, hp] at he
    have hstrict := mul_pos (show 0 < c-(1/2 : ℝ) by linarith) (rowProduct_pos A hn)
    exfalso; nlinarith
  · exact hm

/-- Full equality classification, for every weight and including zero rows. -/
theorem matrix_equality_iff (A : Mat) (c : ℝ) (hc : 0 ≤ c) :
    ‖A.permanent‖ + c*‖A.det‖ = sharpConstant c*rowProduct A ↔
      (∃ i, ∀ j, A i j = 0) ∨
      (IsFlatRankOne A ∧ c ≤ 1/2) ∨ (IsMonomial A ∧ 1/2 ≤ c) := by
  constructor
  · intro he
    by_cases hz : rowProduct A = 0
    · exact Or.inl ((rowProduct_eq_zero_iff A).mp hz)
    · have hn := nonzero_rows_of_rowProduct_ne_zero A hz
      rcases lt_trichotomy c (1/2 : ℝ) with hlt | heq | hgt
      · exact Or.inr (Or.inl ⟨subcritical_equality_only A hn c hlt he, hlt.le⟩)
      · subst c
        have hcrit : ‖A.permanent‖ + (1/2 : ℝ)*‖A.det‖ = (3/2 : ℝ)*rowProduct A := by
          norm_num [sharpConstant] at he
          exact he
        rcases critical_equality_only A hn hcrit with hf | hm
        · exact Or.inr (Or.inl ⟨hf,le_rfl⟩)
        · exact Or.inr (Or.inr ⟨hm,le_rfl⟩)
      · exact Or.inr (Or.inr ⟨supercritical_equality_only A hn c hgt he, hgt.le⟩)
  · rintro (hz | ⟨hf,hc'⟩ | ⟨hm,hc'⟩)
    · have hp := (rowProduct_eq_zero_iff A).mpr hz
      apply le_antisymm (matrix_tradeoff A c hc)
      rw [hp,mul_zero]
      exact add_nonneg (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))
    · obtain ⟨hp,hd⟩ := flat_values A hf
      have hM : sharpConstant c = (3/2 : ℝ) := max_eq_left (by linarith)
      simp only [hp,hd,norm_zero,mul_zero,add_zero,hM]
    · obtain ⟨hp,hd⟩ := monomial_values A hm
      have hM : sharpConstant c = 1+c := max_eq_right (by linarith)
      rw [hp,hd,hM]; ring

/-- The original row-norm spelling of the complete equality classification. -/
theorem sharp_four_row_equality_iff (A : Matrix (Fin 4) (Fin 4) ℂ)
    (c : ℝ) (hc : 0 ≤ c) :
    ‖A.permanent‖ + c*‖A.det‖ = max (3/2) (1+c) *
      (∏ i, Real.sqrt (∑ j, ‖A i j‖^2)) ↔
      (∃ i, ∀ j, A i j = 0) ∨
      (IsFlatRankOne A ∧ c ≤ 1/2) ∨ (IsMonomial A ∧ 1/2 ≤ c) := by
  simpa only [sharpConstant,rowProduct,rowNorm_semantics] using matrix_equality_iff A c hc

/-- Theorem 1: the sharp bound and every equality case, on the actual matrices. -/
theorem sharp_four_row_complete (A : Matrix (Fin 4) (Fin 4) ℂ)
    (c : ℝ) (hc : 0 ≤ c) :
    (‖A.permanent‖ + c*‖A.det‖ ≤ max (3/2) (1+c) *
      (∏ i, Real.sqrt (∑ j, ‖A i j‖^2))) ∧
    ((‖A.permanent‖ + c*‖A.det‖ = max (3/2) (1+c) *
      (∏ i, Real.sqrt (∑ j, ‖A i j‖^2))) ↔
      (∃ i, ∀ j, A i j = 0) ∨
      (IsFlatRankOne A ∧ c ≤ 1/2) ∨ (IsMonomial A ∧ 1/2 ≤ c)) :=
  ⟨sharp_four_row A c hc, sharp_four_row_equality_iff A c hc⟩

#print axioms sharp_four_row_complete
end
end FourRowTradeoff
