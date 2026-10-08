import PermanentBlockPreserve
import OnePointSupport
import Mathlib.GroupTheory.Perm.Finite

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- In a permutation of a disjoint sum, preservation of the right side
is equivalent to membership in the image of the product permutation group. -/
private theorem preservesRight_sum_iff_range
    (σ : Equiv.Perm (α ⊕ β)) :
    (∀ i : β, ∃ j : β, σ (Sum.inr i) = Sum.inr j) ↔
      σ ∈ (Equiv.Perm.sumCongrHom α β).range := by
  constructor
  · intro h
    apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
    apply (Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr σ).mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨j,hj⟩ := h i
    exact ⟨j,hj.symm⟩
  · rintro ⟨⟨p,q⟩,rfl⟩ i
    exact ⟨q i, by simp [Equiv.Perm.sumCongrHom_apply]⟩

/-- For ANY square real matrix on a disjoint union, sum of those
permanent monomials whose permutations preserve the right block
factors as the product of the two principal-block permanents. -/
theorem permanent_contribution_preserving_right
    (M : Matrix (α ⊕ β) (α ⊕ β) ℝ) :
    (∑ σ : Equiv.Perm (α ⊕ β),
      if ∀ i : β, ∃ j : β, σ (Sum.inr i) = Sum.inr j then
        ∏ i : α ⊕ β, M (σ i) i else 0) =
      Matrix.permanent (fun i j : α => M (Sum.inl i) (Sum.inl j)) *
      Matrix.permanent (fun i j : β => M (Sum.inr i) (Sum.inr j)) := by
  classical
  calc
    (∑ σ : Equiv.Perm (α ⊕ β),
      if ∀ i : β, ∃ j : β, σ (Sum.inr i) = Sum.inr j then
        ∏ i : α ⊕ β, M (σ i) i else 0) =
        preservingBlockContribution M := by
          unfold preservingBlockContribution
          apply Finset.sum_congr rfl
          intro σ _
          by_cases h : ∀ i : β, ∃ j : β, σ (Sum.inr i) = Sum.inr j
          · have hr := (preservesRight_sum_iff_range σ).mp h
            simp [h, hr]
          · have hr : σ ∉ (Equiv.Perm.sumCongrHom α β).range := by
              intro hh
              exact h ((preservesRight_sum_iff_range σ).mpr hh)
            simp [h, hr]
    _ = _ := preservingBlockContribution_eq_product M

end Chollet

#print axioms Chollet.permanent_contribution_preserving_right
