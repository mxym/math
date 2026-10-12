import NonnegativePivot

namespace Chollet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every individual permanent permutation monomial is invariant under
diagonal sign conjugation. This is stronger than mere permanent invariance. -/
theorem signedSwitch_perm_term
    (A : Matrix n n ℝ) (s : n → ℝ)
    (hs : ∀ i, (s i)^2 = 1)
    (σ : Equiv.Perm n) :
    (∏ i, signedSwitch A s (σ i) i) =
      (∏ i, A (σ i) i) := by
  classical
  have hsp : (∏ i, s i)^2 = 1 := by
    rw [← Finset.prod_pow]
    simp only [hs]
    simp
  have hp : (∏ i, s (σ i)) = ∏ i, s i :=
    Equiv.prod_comp σ s
  calc
    (∏ i, signedSwitch A s (σ i) i)
        = (∏ i, s (σ i)) * (∏ i, A (σ i) i) * (∏ i, s i) := by
            simp only [signedSwitch, Finset.prod_mul_distrib, mul_assoc]
    _ = (∏ i, A (σ i) i) * ((∏ i, s i)^2) := by rw [hp]; ring
    _ = (∏ i, A (σ i) i) := by rw [hsp]; ring

/-- The singleton permanent pivot bound for any matrix that can be
made entrywise nonnegative by diagonal conjugation with ±1 signs. -/
theorem permanent_optionPivot_of_signSwitch_nonnegative
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix (Option α) (Option α) ℝ)
    (s : Option α → ℝ)
    (hs : ∀ i, (s i)^2 = 1)
    (h_nonneg : ∀ i j, 0 ≤ signedSwitch M s i j) :
    M none none * Matrix.permanent (fun i j : α => M (some i) (some j)) ≤
      Matrix.permanent M := by
  classical
  have hterm (σ : Equiv.Perm (Option α)) :
      0 ≤ ∏ i, M (σ i) i := by
    rw [← signedSwitch_perm_term M s hs σ]
    apply Finset.prod_nonneg
    intro i _
    exact h_nonneg (σ i) i
  calc
    M none none * Matrix.permanent (fun i j : α => M (some i) (some j)) =
      (∑ σ : Equiv.Perm (Option α),
        if σ none = none then
          ∏ i : Option α, M (σ i) i else 0) :=
            (option_root_fixed_contribution M).symm
    _ ≤ ∑ σ : Equiv.Perm (Option α),
        ∏ i : Option α, M (σ i) i := by
          apply Finset.sum_le_sum
          intro σ _
          by_cases hf : σ none = none
          · simp [hf]
          · simpa [hf] using hterm σ
    _ = Matrix.permanent M := rfl

end Chollet

#print axioms Chollet.signedSwitch_perm_term
#print axioms Chollet.permanent_optionPivot_of_signSwitch_nonnegative
