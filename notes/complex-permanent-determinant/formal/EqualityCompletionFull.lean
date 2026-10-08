import EqualitySufficiencyVerified
import EqualityMonomialVerified

namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilAbsolute

noncomputable section

def absoluteSquaredSaturated
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) : Prop :=
  (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖ +
     detWeight * ‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
    (4/3 : ℝ) * rowSq a0 a1 a2 *
       rowSq b0 b1 b2 * rowSq c0 c1 c2

theorem rowSq_nonneg_all (a0 a1 a2 : ℂ) :
    0 ≤ rowSq a0 a1 a2 := by
  unfold rowSq
  have h0 := ComplexPencilLink.sq_nonneg a0
  have h1 := ComplexPencilLink.sq_nonneg a1
  have h2 := ComplexPencilLink.sq_nonneg a2
  linarith

theorem zero_row_iff (a0 a1 a2 : ℂ) :
    rowSq a0 a1 a2 = 0 ↔
      a0 = 0 ∧ a1 = 0 ∧ a2 = 0 := by
  constructor
  · intro h
    have h0 := ComplexPencilLink.sq_nonneg a0
    have h1 := ComplexPencilLink.sq_nonneg a1
    have h2 := ComplexPencilLink.sq_nonneg a2
    have hz0 : ComplexPencilLink.sq a0 = 0 := by
      unfold rowSq at h
      linarith
    have hz1 : ComplexPencilLink.sq a1 = 0 := by
      unfold rowSq at h
      linarith
    have hz2 : ComplexPencilLink.sq a2 = 0 := by
      unfold rowSq at h
      linarith
    exact ⟨link_sq_zero a0 hz0,
           link_sq_zero a1 hz1,
           link_sq_zero a2 hz2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [rowSq, ComplexPencilLink.sq]

theorem saturated_first_zero
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (h : a0 = 0 ∧ a1 = 0 ∧ a2 = 0) :
    absoluteSquaredSaturated a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  rcases h with ⟨rfl,rfl,rfl⟩
  simp [absoluteSquaredSaturated, permanent3, determinant3,
    rowSq, ComplexPencilLink.sq]

theorem saturated_second_zero
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (h : b0 = 0 ∧ b1 = 0 ∧ b2 = 0) :
    absoluteSquaredSaturated a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  rcases h with ⟨rfl,rfl,rfl⟩
  simp [absoluteSquaredSaturated, permanent3, determinant3,
    rowSq, ComplexPencilLink.sq]

theorem saturated_third_zero
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (h : c0 = 0 ∧ c1 = 0 ∧ c2 = 0) :
    absoluteSquaredSaturated a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  rcases h with ⟨rfl,rfl,rfl⟩
  simp [absoluteSquaredSaturated, permanent3, determinant3,
    rowSq, ComplexPencilLink.sq]

/-- Complete equality-case classification for the sharp complex
three-row absolute-value permanent--determinant theorem.
The first three alternatives are the zero-row cases, the fourth
is the nonzero balanced rank-one class, and the fifth is the
nonzero complex monomial class. -/
theorem absolute_equality_iff_full
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    absoluteSquaredSaturated a0 a1 a2 b0 b1 b2 c0 c1 c2 ↔
      (a0 = 0 ∧ a1 = 0 ∧ a2 = 0) ∨
      (b0 = 0 ∧ b1 = 0 ∧ b2 = 0) ∨
      (c0 = 0 ∧ c1 = 0 ∧ c2 = 0) ∨
      flatRankOne a0 a1 a2 b0 b1 b2 c0 c1 c2 ∨
      monomialRows a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  constructor
  · intro heq
    by_cases ha : 0 < rowSq a0 a1 a2
    · by_cases hb : 0 < rowSq b0 b1 b2
      · by_cases hc : 0 < rowSq c0 c1 c2
        · rcases equality_nonzero_rankone_or_monomial
            a0 a1 a2 b0 b1 b2 c0 c1 c2 ha hb hc heq with hr | hm
          · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hm)))
        · have hz : rowSq c0 c1 c2 = 0 :=
            le_antisymm (le_of_not_gt hc) (rowSq_nonneg_all c0 c1 c2)
          exact Or.inr (Or.inr (Or.inl ((zero_row_iff c0 c1 c2).mp hz)))
      · have hz : rowSq b0 b1 b2 = 0 :=
          le_antisymm (le_of_not_gt hb) (rowSq_nonneg_all b0 b1 b2)
        exact Or.inr (Or.inl ((zero_row_iff b0 b1 b2).mp hz))
    · have hz : rowSq a0 a1 a2 = 0 :=
        le_antisymm (le_of_not_gt ha) (rowSq_nonneg_all a0 a1 a2)
      exact Or.inl ((zero_row_iff a0 a1 a2).mp hz)
  · intro hcases
    rcases hcases with hz | hz | hz | hflat | hmon
    · exact saturated_first_zero a0 a1 a2 b0 b1 b2 c0 c1 c2 hz
    · exact saturated_second_zero a0 a1 a2 b0 b1 b2 c0 c1 c2 hz
    · exact saturated_third_zero a0 a1 a2 b0 b1 b2 c0 c1 c2 hz
    · exact flatRankOne_saturates_verified a0 a1 a2 b0 b1 b2 c0 c1 c2 hflat
    · exact monomialRows_saturates_verified a0 a1 a2 b0 b1 b2 c0 c1 c2 hmon

#print axioms ComplexPencilEquality.absolute_equality_iff_full

end
end ComplexPencilEquality
