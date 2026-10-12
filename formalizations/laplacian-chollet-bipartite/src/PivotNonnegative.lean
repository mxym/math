import OnePointRoot
import Signed
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace Chollet

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Singleton permanent pivot lower bound for an arbitrary
entrywise-nonnegative Option-indexed real matrix. Uses the actual permanent
and principal deletion; no PSD hypothesis or external Lieb theorem. -/
theorem permanent_root_pivot_of_nonnegative
    (M : Matrix (Option α) (Option α) ℝ)
    (hn : ∀ i j, 0 ≤ M i j) :
    M none none *
      Matrix.permanent (fun i j : α => M (some i) (some j)) ≤
    Matrix.permanent M := by
  classical
  calc
    M none none *
      Matrix.permanent (fun i j : α => M (some i) (some j)) =
      (∑ σ : Equiv.Perm (Option α),
        if σ none = none then
          ∏ i : Option α, M (σ i) i else 0) :=
        (option_root_fixed_contribution M).symm
    _ ≤ ∑ σ : Equiv.Perm (Option α), ∏ i : Option α, M (σ i) i := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hf : σ none = none
      · simp [hf]
      · simp only [if_neg hf]
        apply Finset.prod_nonneg
        intro i _
        exact hn (σ i) i
    _ = Matrix.permanent M := rfl

end Chollet

#print axioms Chollet.permanent_root_pivot_of_nonnegative
