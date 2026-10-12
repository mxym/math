import OnePointRightEquiv

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Rebracket the distinguished root with the right block, leaving
the left non-root block as the other component. -/
def onePointLeftEquiv : Option β ⊕ α ≃ Option (α ⊕ β) where
  toFun
    | .inl none => none
    | .inl (some j) => some (.inr j)
    | .inr i => some (.inl i)
  invFun
    | none => .inl none
    | some (.inl i) => .inr i
    | some (.inr j) => .inl (some j)
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

private theorem onePointLeft_perm_congr_preserve
    (σ : Equiv.Perm (Option β ⊕ α)) :
    preservesLeft (onePointLeftEquiv.permCongr σ) ↔
      (∀ i : α, ∃ j : α, σ (Sum.inr i) = Sum.inr j) := by
  constructor
  · intro h i
    obtain ⟨j,hj⟩ := h i
    refine ⟨j, onePointLeftEquiv.injective ?_⟩
    simpa [Equiv.permCongr_apply, onePointLeftEquiv] using hj
  · intro h i
    obtain ⟨j,hj⟩ := h i
    refine ⟨j, ?_⟩
    simpa [Equiv.permCongr_apply, onePointLeftEquiv] using
      congrArg onePointLeftEquiv hj

private theorem onePointLeft_perm_term_reindex
    (M : Matrix (Option (α ⊕ β)) (Option (α ⊕ β)) ℝ)
    (σ : Equiv.Perm (Option β ⊕ α)) :
    (∏ i : Option (α ⊕ β),
        M ((onePointLeftEquiv.permCongr σ) i) i) =
      (∏ i : Option β ⊕ α,
        M (onePointLeftEquiv (σ i)) (onePointLeftEquiv i)) := by
  rw [← Equiv.prod_comp onePointLeftEquiv
      (fun i => M ((onePointLeftEquiv.permCongr σ) i) i)]
  apply Finset.prod_congr rfl
  intro i _
  simp [Equiv.permCongr_apply]

attribute [local instance] Classical.propDecidable

/-- The total permanent contribution from permutations preserving the
left non-root block. This is the right-hand analogue of the previous
decomposition, including the shared root diagonal sum. -/
theorem onePointSum_preservingLeft_contribution
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ) :
    (∑ σ : Equiv.Perm (Option (α ⊕ β)),
      if preservesLeft σ then
        ∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i else 0) =
      Matrix.permanent (diagonalBump B none (A none none)) *
        Matrix.permanent (fun i j : α => A (some i) (some j)) := by
  classical
  let M := onePointSumMatrix A B
  let e : Option β ⊕ α ≃ Option (α ⊕ β) := onePointLeftEquiv
  let N : Matrix (Option β ⊕ α) (Option β ⊕ α) ℝ :=
    fun i j => M (e i) (e j)
  have hsum :
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        if preservesLeft σ then
          ∏ i : Option (α ⊕ β), M (σ i) i else 0) =
      (∑ τ : Equiv.Perm (Option β ⊕ α),
        if ∀ i : α, ∃ j : α, τ (Sum.inr i) = Sum.inr j then
          ∏ i : Option β ⊕ α, N (τ i) i else 0) := by
    symm
    apply Fintype.sum_equiv (e.permCongr)
    intro τ
    by_cases hr : ∀ i : α, ∃ j : α, τ (Sum.inr i) = Sum.inr j
    · have hs : preservesLeft (e.permCongr τ) :=
        (onePointLeft_perm_congr_preserve τ).mpr hr
      simp only [if_pos hr, if_pos hs]
      exact (onePointLeft_perm_term_reindex M τ).symm
    · have hs : ¬ preservesLeft (e.permCongr τ) := by
        intro h
        exact hr ((onePointLeft_perm_congr_preserve τ).mp h)
      simp [hr, hs]
  have hleft :
      (fun i j : Option β => N (Sum.inl i) (Sum.inl j)) =
        diagonalBump B none (A none none) := by
    ext i j
    cases i <;> cases j <;>
      simp [N, e, M, onePointLeftEquiv, onePointSumMatrix, diagonalBump] <;> ring
  have hright :
      (fun i j : α => N (Sum.inr i) (Sum.inr j)) =
        (fun i j : α => A (some i) (some j)) := by rfl
  calc
    (∑ σ : Equiv.Perm (Option (α ⊕ β)),
      if preservesLeft σ then
        ∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i else 0) =
      (∑ τ : Equiv.Perm (Option β ⊕ α),
        if ∀ i : α, ∃ j : α, τ (Sum.inr i) = Sum.inr j then
          ∏ i : Option β ⊕ α, N (τ i) i else 0) := hsum
    _ = Matrix.permanent (fun i j : Option β => N (Sum.inl i) (Sum.inl j)) *
        Matrix.permanent (fun i j : α => N (Sum.inr i) (Sum.inr j)) :=
      permanent_contribution_preserving_right N
    _ = _ := by rw [hleft, hright]

end Chollet

#print axioms Chollet.onePointSum_preservingLeft_contribution
