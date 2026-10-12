import OnePointPermClass
import Reindex
import CofactorOption
import PermanentDiagonalMinor

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Rebracket the root plus the left block as one side, and the right
non-root block as the other side. -/
def onePointRightEquiv : Option α ⊕ β ≃ Option (α ⊕ β) where
  toFun
    | .inl none => none
    | .inl (some i) => some (.inl i)
    | .inr j => some (.inr j)
  invFun
    | none => .inl none
    | some (.inl i) => .inl (some i)
    | some (.inr j) => .inr j
  left_inv := by
    intro x
    rcases x with x | x
    · cases x <;> rfl
    · rfl
  right_inv := by
    intro x
    rcases x with _ | x
    · rfl
    · cases x <;> rfl

private theorem onePointRight_perm_congr_preserve
    (σ : Equiv.Perm (Option α ⊕ β)) :
    preservesRight (onePointRightEquiv.permCongr σ) ↔
      (∀ i : β, ∃ j : β, σ (Sum.inr i) = Sum.inr j) := by
  constructor
  · intro h i
    obtain ⟨j,hj⟩ := h i
    refine ⟨j, onePointRightEquiv.injective ?_⟩
    simpa [Equiv.permCongr_apply, onePointRightEquiv] using hj
  · intro h i
    obtain ⟨j,hj⟩ := h i
    refine ⟨j, ?_⟩
    change (onePointRightEquiv.permCongr σ) (some (.inr i)) = some (.inr j)
    simpa [Equiv.permCongr_apply, onePointRightEquiv] using
      congrArg onePointRightEquiv hj

private theorem onePointRight_perm_term_reindex
    (M : Matrix (Option (α ⊕ β)) (Option (α ⊕ β)) ℝ)
    (σ : Equiv.Perm (Option α ⊕ β)) :
    (∏ i : Option (α ⊕ β),
        M ((onePointRightEquiv.permCongr σ) i) i) =
      (∏ i : Option α ⊕ β,
        M (onePointRightEquiv (σ i)) (onePointRightEquiv i)) := by
  rw [← Equiv.prod_comp onePointRightEquiv
      (fun i => M ((onePointRightEquiv.permCongr σ) i) i)]
  apply Finset.prod_congr rfl
  intro i _
  simp [Equiv.permCongr_apply]


attribute [local instance] Classical.propDecidable

/-- Exact one-point-sum contribution from all permutations preserving
the right non-root block. -/
theorem onePointSum_preservingRight_contribution
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ) :
    (∑ σ : Equiv.Perm (Option (α ⊕ β)),
      if preservesRight σ then
        ∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i else 0) =
      Matrix.permanent (diagonalBump A none (B none none)) *
        Matrix.permanent (fun i j : β => B (some i) (some j)) := by
  classical
  let M := onePointSumMatrix A B
  let e : Option α ⊕ β ≃ Option (α ⊕ β) := onePointRightEquiv
  let N : Matrix (Option α ⊕ β) (Option α ⊕ β) ℝ :=
    fun i j => M (e i) (e j)
  have hsum :
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        if preservesRight σ then
          ∏ i : Option (α ⊕ β), M (σ i) i else 0) =
      (∑ τ : Equiv.Perm (Option α ⊕ β),
        if ∀ i : β, ∃ j : β, τ (Sum.inr i) = Sum.inr j then
          ∏ i : Option α ⊕ β, N (τ i) i else 0) := by
    symm
    apply Fintype.sum_equiv (e.permCongr)
    intro τ
    by_cases hr : ∀ i : β, ∃ j : β, τ (Sum.inr i) = Sum.inr j
    · have hs : preservesRight (e.permCongr τ) :=
        (onePointRight_perm_congr_preserve τ).mpr hr
      simp only [if_pos hr, if_pos hs]
      exact (onePointRight_perm_term_reindex M τ).symm
    · have hs : ¬ preservesRight (e.permCongr τ) := by
        intro h
        exact hr ((onePointRight_perm_congr_preserve τ).mp h)
      simp [hr, hs]
  have hleft :
      (fun i j : Option α => N (Sum.inl i) (Sum.inl j)) =
        diagonalBump A none (B none none) := by
    ext i j
    cases i <;> cases j <;>
      simp [N, e, M, onePointRightEquiv, onePointSumMatrix, diagonalBump]
  have hright :
      (fun i j : β => N (Sum.inr i) (Sum.inr j)) =
        (fun i j : β => B (some i) (some j)) := by
    rfl
  calc
    (∑ σ : Equiv.Perm (Option (α ⊕ β)),
      if preservesRight σ then
        ∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i else 0) =
      (∑ τ : Equiv.Perm (Option α ⊕ β),
        if ∀ i : β, ∃ j : β, τ (Sum.inr i) = Sum.inr j then
          ∏ i : Option α ⊕ β, N (τ i) i else 0) := hsum
    _ = Matrix.permanent (fun i j : Option α => N (Sum.inl i) (Sum.inl j)) *
        Matrix.permanent (fun i j : β => N (Sum.inr i) (Sum.inr j)) :=
      permanent_contribution_preserving_right N
    _ = _ := by rw [hleft, hright]

end Chollet
