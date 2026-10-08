import OnePointStrongClosure
import OnePointPivotClosure
import PermanentDirectSumStability
import PermanentDirectSum

namespace Chollet

/-- An exact rooted matrix invariant designed for induction over
one-vertex graph-block coalescences. Each field is a genuine inequality
for the Mathlib permanent, with no positivity hidden in a class axiom. -/
structure RootedStrong
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix (Option α) (Option α) ℝ) : Prop where
  diag_nonneg : ∀ i, 0 ≤ A i i
  strong :
    Matrix.permanent (fun i j => A i j * A i j) ≤
      Matrix.permanent A * (∏ i, A i i)
  deleted_strong :
    Matrix.permanent (fun i j : α =>
        A (some i) (some j) * A (some i) (some j)) ≤
      Matrix.permanent (fun i j : α => A (some i) (some j)) *
        (∏ i : α, A (some i) (some i))
  deleted_nonneg :
    0 ≤ Matrix.permanent (fun i j : α => A (some i) (some j))
  pivot :
    A none none *
      Matrix.permanent (fun i j : α => A (some i) (some j)) ≤
      Matrix.permanent A

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The complete rooted strong-Chollet invariant is preserved by any
single-vertex coalescence of two finite real matrices.

This is a true arbitrary-order matrix composition theorem, suitable for
iterated vertex-gluing constructions, not just a scalar inequality. -/
theorem RootedStrong.onePointSum
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ)
    (hA : RootedStrong A) (hB : RootedStrong B) :
    RootedStrong (onePointSumMatrix A B) := by
  classical
  let C := onePointSumMatrix A B
  let A0 : Matrix α α ℝ := fun i j => A (some i) (some j)
  let B0 : Matrix β β ℝ := fun i j => B (some i) (some j)
  let C0 : Matrix (α ⊕ β) (α ⊕ β) ℝ :=
    fun i j => C (some i) (some j)
  have hdecomp : C0 = directSumMatrix A0 B0 := by
    ext i j
    cases i <;> cases j <;> rfl
  have hdiag : ∀ i, 0 ≤ C i i := by
    intro i
    cases i with
    | none =>
      change 0 ≤ A none none + B none none
      exact add_nonneg (hA.diag_nonneg none) (hB.diag_nonneg none)
    | some x =>
      cases x with
      | inl x => exact hA.diag_nonneg (some x)
      | inr x => exact hB.diag_nonneg (some x)
  have hs :
      Matrix.permanent (fun i j => C i j * C i j) ≤
        Matrix.permanent C * (∏ i, C i i) :=
    strongChollet_onePointSum_of_pivot A B
      hA.diag_nonneg hB.diag_nonneg
      hA.strong hB.strong
      hA.deleted_strong hB.deleted_strong
      hA.deleted_nonneg hB.deleted_nonneg
      hA.pivot hB.pivot
  have hds :
      Matrix.permanent (fun i j : α ⊕ β => C0 i j * C0 i j) ≤
        Matrix.permanent C0 * (∏ i, C0 i i) := by
    rw [hdecomp]
    exact strongChollet_directSumMatrix A0 B0
      hA.deleted_strong hB.deleted_strong
  have hdn : 0 ≤ Matrix.permanent C0 := by
    rw [hdecomp, permanent_directSumMatrix]
    exact mul_nonneg hA.deleted_nonneg hB.deleted_nonneg
  have hpivot :
      C none none * Matrix.permanent C0 ≤ Matrix.permanent C :=
    onePointSum_rootPivot_of_blockPivots A B
      hA.deleted_nonneg hB.deleted_nonneg hA.pivot hB.pivot
  exact {
    diag_nonneg := hdiag
    strong := hs
    deleted_strong := hds
    deleted_nonneg := hdn
    pivot := hpivot
  }

end Chollet

#print axioms Chollet.RootedStrong.onePointSum
