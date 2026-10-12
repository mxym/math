import OnePointRoot
import Signed

namespace Chollet

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A matrix with nonnegative entries satisfies the Lieb singleton
permanent pivot bound at the distinguished Option.none index,
without assuming PSD or symmetry. The proof is a *termwise*
inequality over actual permutation monomials. -/
theorem permanent_optionPivot_of_nonnegative
    (M : Matrix (Option α) (Option α) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) :
    M none none * Matrix.permanent (fun i j : α => M (some i) (some j)) ≤
      Matrix.permanent M := by
  classical
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
          by_cases hs : σ none = none
          · simp [hs]
          · have ht : 0 ≤ ∏ i : Option α, M (σ i) i := by
              apply Finset.prod_nonneg
              intro i _
              exact hM (σ i) i
            simpa [hs] using ht
    _ = Matrix.permanent M := rfl

end Chollet

#print axioms Chollet.permanent_optionPivot_of_nonnegative
