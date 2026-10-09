import FourRowSharpness
open scoped BigOperators
namespace FourRowTradeoff
noncomputable section

/-- The actual normalized pencil values in the supremum in Corollary 2. -/
def pencilValues (t : ℝ) : Set ℝ :=
  {x | ∃ A : Mat, 0 < rowProduct A ∧
    x = ‖A.permanent+(t : ℂ)*A.det‖ / rowProduct A}

theorem pencil_attainment (t : ℝ) :
    ∃ A : Mat, 0 < rowProduct A ∧
      ‖A.permanent+(t : ℂ)*A.det‖ = sharpConstant |t| * rowProduct A := by
  by_cases h : 1+|t| ≤ 3/2
  · refine ⟨flatMatrix, ?_, ?_⟩
    · rw [flat_rowProduct]; norm_num
    · rw [flat_pencil, flat_rowProduct, sharpConstant, max_eq_left h]
      norm_num
  · have hm : sharpConstant |t| = 1+|t| := max_eq_right (by linarith)
    by_cases ht : 0 ≤ t
    · refine ⟨1, ?_, ?_⟩
      · rw [one_rowProduct]; norm_num
      · rw [one_pencil, one_rowProduct, mul_one, hm, abs_of_nonneg ht,
          abs_of_nonneg (by linarith : 0 ≤ 1+t)]
    · refine ⟨oddMatrix, ?_, ?_⟩
      · rw [odd_rowProduct]; norm_num
      · rw [odd_pencil, odd_rowProduct, mul_one, hm,
          abs_of_nonpos (by linarith : t ≤ 0), abs_of_nonneg (by linarith : 0 ≤ 1-t)]
        ring

/-- An attained greatest value, not merely a bound on an auxiliary expression. -/
theorem pencil_norm_isGreatest (t : ℝ) :
    IsGreatest (pencilValues t) (max (3/2) (1+|t|)) := by
  constructor
  · obtain ⟨A, hp, ha⟩ := pencil_attainment t
    refine ⟨A, hp, ?_⟩
    rw [ha]
    simp only [sharpConstant, mul_div_cancel_right₀ _ (ne_of_gt hp)]
  · rintro x ⟨A, hp, rfl⟩
    apply (div_le_iff₀ hp).2
    exact pencil_bound A t

/-- The exact supremum in the source paper, for every real parameter. -/
theorem exact_real_pencil_norm (t : ℝ) :
    sSup (pencilValues t) = max (3/2) (1+|t|) :=
  (pencil_norm_isGreatest t).csSup_eq

/-- The actual normalized values of the simultaneous permanent/determinant objective. -/
def tradeoffValues (c : ℝ) : Set ℝ :=
  {x | ∃ A : Mat, 0 < rowProduct A ∧
    x = (‖A.permanent‖+c*‖A.det‖) / rowProduct A}

theorem tradeoff_isGreatest (c : ℝ) (hc : 0 ≤ c) :
    IsGreatest (tradeoffValues c) (max (3/2) (1+c)) := by
  constructor
  · obtain ⟨A, hp, ha⟩ := matrix_attainment c
    refine ⟨A, hp, ?_⟩
    rw [ha]
    simp only [sharpConstant, mul_div_cancel_right₀ _ (ne_of_gt hp)]
  · rintro x ⟨A, hp, rfl⟩
    apply (div_le_iff₀ hp).2
    exact matrix_tradeoff A c hc

theorem exact_tradeoff_norm (c : ℝ) (hc : 0 ≤ c) :
    sSup (tradeoffValues c) = max (3/2) (1+c) :=
  (tradeoff_isGreatest c hc).csSup_eq

#print axioms exact_real_pencil_norm
#print axioms exact_tradeoff_norm
end
end FourRowTradeoff
