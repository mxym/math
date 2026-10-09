import PermanentDirectSum
import Mathlib.GroupTheory.Perm.Finite

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]

/-- Contribution to a real matrix permanent of exactly those permutations
which preserve the two blocks of the index-set sum. -/
def preservingBlockContribution (M : Matrix (α ⊕ β) (α ⊕ β) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (α ⊕ β),
    if σ ∈ (Equiv.Perm.sumCongrHom α β).range then
      ∏ i : α ⊕ β, M (σ i) i
    else 0

/-- The sum over block-preserving permutations factors for ANY real matrix,
even if its off-diagonal blocks contain arbitrary entries. -/
theorem preservingBlockContribution_eq_product
    (M : Matrix (α ⊕ β) (α ⊕ β) ℝ) :
    preservingBlockContribution M =
      Matrix.permanent (fun i j : α => M (Sum.inl i) (Sum.inl j)) *
      Matrix.permanent (fun i j : β => M (Sum.inr i) (Sum.inr j)) := by
  classical
  let H := (Equiv.Perm.sumCongrHom α β).range
  let F : Equiv.Perm (α ⊕ β) → ℝ :=
    fun σ => ∏ i : α ⊕ β, M (σ i) i
  have hmap :
      (∑ p : Equiv.Perm α × Equiv.Perm β,
        F ((Equiv.Perm.sumCongrHom α β) p)) =
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (α ⊕ β))) with σ ∈ H,
        F σ) := by
    apply Finset.sum_bij (fun p _ => (Equiv.Perm.sumCongrHom α β) p)
    · intro p _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, rfl⟩
    · intro p _ q _ heq
      exact Equiv.Perm.sumCongrHom_injective heq
    · intro σ hσ
      obtain ⟨p,hp⟩ := (Finset.mem_filter.mp hσ).2
      exact ⟨p, Finset.mem_univ _, hp⟩
    · intro p _
      rfl
  have hterm (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
      (∏ i : α ⊕ β, M ((σ.sumCongr τ) i) i) =
        (∏ i : α, M (Sum.inl (σ i)) (Sum.inl i)) *
        (∏ i : β, M (Sum.inr (τ i)) (Sum.inr i)) := by
    rw [Fintype.prod_sum_type]
    simp [Equiv.Perm.sumCongr_apply]
  calc
    preservingBlockContribution M =
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (α ⊕ β))) with σ ∈ H,
        F σ) := by
          unfold preservingBlockContribution F
          rw [Finset.sum_filter]
    _ = (∑ p : Equiv.Perm α × Equiv.Perm β,
        F ((Equiv.Perm.sumCongrHom α β) p)) := hmap.symm
    _ = Matrix.permanent (fun i j : α => M (Sum.inl i) (Sum.inl j)) *
        Matrix.permanent (fun i j : β => M (Sum.inr i) (Sum.inr j)) := by
          simp only [F, Equiv.Perm.sumCongrHom_apply,
            hterm, Fintype.sum_prod_type]
          simp only [Matrix.permanent]
          rw [Finset.sum_mul]
          congr 1
          ext σ
          rw [Finset.mul_sum]

end Chollet

#print axioms Chollet.preservingBlockContribution_eq_product
