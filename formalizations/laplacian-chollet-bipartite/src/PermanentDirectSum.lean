import Mathlib.GroupTheory.Perm.Finite
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Real.Basic

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Actual block-diagonal real matrix indexed by the sum of two finite types. -/
def directSumMatrix (A : Matrix α α ℝ) (B : Matrix β β ℝ) :
    Matrix (α ⊕ β) (α ⊕ β) ℝ :=
  fun i j => match i,j with
    | .inl x, .inl y => A x y
    | .inr x, .inr y => B x y
    | _,_ => 0

private theorem directSum_term_sumCongr
    (A : Matrix α α ℝ) (B : Matrix β β ℝ)
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    (∏ i : α ⊕ β, directSumMatrix A B ((σ.sumCongr τ) i) i) =
      (∏ i : α, A (σ i) i) * (∏ i : β, B (τ i) i) := by
  rw [Fintype.prod_sum_type]
  simp [directSumMatrix, Equiv.Perm.sumCongr_apply]

private theorem directSum_term_zero_of_left_mixing
    (A : Matrix α α ℝ) (B : Matrix β β ℝ)
    (σ : Equiv.Perm (α ⊕ β))
    (hmix : ¬ ∀ i : α, ∃ j : α, σ (Sum.inl i) = Sum.inl j) :
    (∏ i : α ⊕ β, directSumMatrix A B (σ i) i) = 0 := by
  classical
  obtain ⟨i, hbad⟩ := not_forall.mp hmix
  cases hσ : σ (Sum.inl i) with
  | inl j =>
    exact (hbad ⟨j, hσ⟩).elim
  | inr j =>
    have hz : directSumMatrix A B (σ (Sum.inl i)) (Sum.inl i) = 0 := by
      simp [directSumMatrix, hσ]
    exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i)) hz


/-- General multiplicativity of the REAL matrix permanent on a direct sum
of any finite square matrices. No positivity/PSD assumption. -/
theorem permanent_directSumMatrix
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) :
    Matrix.permanent (directSumMatrix A B) =
      Matrix.permanent A * Matrix.permanent B := by
  classical
  let H := (Equiv.Perm.sumCongrHom α β).range
  let F : Equiv.Perm (α ⊕ β) → ℝ :=
    fun σ => ∏ i : α ⊕ β, directSumMatrix A B (σ i) i
  have hzero (σ : Equiv.Perm (α ⊕ β)) (hnot : σ ∉ H) :
      F σ = 0 := by
    apply directSum_term_zero_of_left_mixing A B σ
    intro hp
    apply hnot
    apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hp i
    exact ⟨j, hj.symm⟩
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
      obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hσ).2
      refine ⟨p, Finset.mem_univ _, ?_⟩
      exact hp
    · intro p _
      rfl
  calc
    Matrix.permanent (directSumMatrix A B) =
        ∑ σ : Equiv.Perm (α ⊕ β), F σ := rfl
    _ = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (α ⊕ β))) with σ ∈ H,
        F σ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro σ _
          by_cases hh : σ ∈ H
          · simp [hh]
          · simp [hh, hzero σ hh]
    _ = ∑ p : Equiv.Perm α × Equiv.Perm β,
        F ((Equiv.Perm.sumCongrHom α β) p) := hmap.symm
    _ = Matrix.permanent A * Matrix.permanent B := by
      simp only [F, Equiv.Perm.sumCongrHom_apply,
        directSum_term_sumCongr, Fintype.sum_prod_type]
      simp only [Matrix.permanent]
      rw [Finset.sum_mul]
      congr 1
      ext σ
      rw [Finset.mul_sum]

#print axioms Chollet.permanent_directSumMatrix

end Chollet
