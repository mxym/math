import PermanentOnePointStrong
import PermanentDirectSumStability
import PermanentDirectSum

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Exact hereditary-at-a-distinguished-root hypothesis for arbitrary
finite real matrices. It is stronger than strong Chollet at a single root,
and carefully exposes the pivot and minor-permanent properties. -/
structure RootStrong (A : Matrix (Option α) (Option α) ℝ) : Prop where
  diag_nonneg : ∀ i : Option α, 0 ≤ A i i
  whole : Matrix.permanent (fun i j => A i j*A i j) ≤
    Matrix.permanent A * (∏ i, A i i)
  deleted : Matrix.permanent
      (fun i j : α => A (some i) (some j)*A (some i) (some j)) ≤
    Matrix.permanent (fun i j : α => A (some i) (some j)) *
      (∏ i : α, A (some i) (some i))
  pivot : A none none *
      Matrix.permanent (fun i j : α => A (some i) (some j)) ≤
    Matrix.permanent A
  deleted_nonneg :
    0 ≤ Matrix.permanent (fun i j : α => A (some i) (some j))

/-- Rooted strong Chollet, including the root pivot and the deleted
principal bound, is CLOSED under single-vertex coalescence, for arbitrary
finite real matrix sizes and without a PSD/Lieb assumption. -/
theorem RootStrong.onePointSum
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ)
    (hA : RootStrong A) (hB : RootStrong B) :
    RootStrong (onePointSumMatrix A B) := by
  classical
  let AR : Matrix α α ℝ := fun i j => A (some i) (some j)
  let BR : Matrix β β ℝ := fun i j => B (some i) (some j)
  let C := onePointSumMatrix A B
  have hrest :
      (fun i j : α ⊕ β => C (some i) (some j)) =
        directSumMatrix AR BR := by
    ext i j
    cases i <;> cases j <;> rfl
  have hminor : Matrix.permanent (fun i j : α ⊕ β =>
      C (some i) (some j)*C (some i) (some j)) ≤
      Matrix.permanent (fun i j : α ⊕ β => C (some i) (some j)) *
        (∏ i : α ⊕ β, C (some i) (some i)) := by
    have hh := strongChollet_directSumMatrix AR BR hA.deleted hB.deleted
    rw [← hrest] at hh
    exact hh
  have hrestper :
      Matrix.permanent (fun i j : α ⊕ β => C (some i) (some j)) =
        Matrix.permanent AR * Matrix.permanent BR := by
    calc
      _ = Matrix.permanent (directSumMatrix AR BR) :=
        congrArg Matrix.permanent hrest
      _ = _ := permanent_directSumMatrix AR BR
  have hnrest :
      0 ≤ Matrix.permanent (fun i j : α ⊕ β => C (some i) (some j)) := by
    rw [hrestper]
    exact mul_nonneg hA.deleted_nonneg hB.deleted_nonneg
  have hdiag : ∀ i : Option (α ⊕ β), 0 ≤ C i i := by
    intro i
    cases i with
    | none =>
      exact add_nonneg (hA.diag_nonneg none) (hB.diag_nonneg none)
    | some i =>
      cases i with
      | inl j => exact hA.diag_nonneg (some j)
      | inr j => exact hB.diag_nonneg (some j)
  have hwhole : Matrix.permanent (fun i j => C i j*C i j) ≤
      Matrix.permanent C * (∏ i, C i i) :=
    strongChollet_onePointSum_of_pivots A B
      hA.whole hB.whole hA.deleted hB.deleted
      hA.pivot hB.pivot hA.deleted_nonneg hB.deleted_nonneg
      hA.diag_nonneg hB.diag_nonneg
  have hpivot :
      C none none *
        Matrix.permanent (fun i j : α ⊕ β => C (some i) (some j)) ≤
          Matrix.permanent C := by
    have hper := permanent_onePointSumMatrix A B
    have hmulA :
        A none none * Matrix.permanent AR * Matrix.permanent BR ≤
          Matrix.permanent A * Matrix.permanent BR :=
      mul_le_mul_of_nonneg_right hA.pivot hB.deleted_nonneg
    have hmulB :
        B none none * Matrix.permanent BR * Matrix.permanent AR ≤
          Matrix.permanent B * Matrix.permanent AR :=
      mul_le_mul_of_nonneg_right hB.pivot hA.deleted_nonneg
    calc
      C none none *
        Matrix.permanent (fun i j : α ⊕ β => C (some i) (some j)) =
          (A none none + B none none) *
            (Matrix.permanent AR * Matrix.permanent BR) := by
              rw [hrestper]; rfl
      _ = A none none * Matrix.permanent AR * Matrix.permanent BR +
          B none none * Matrix.permanent BR * Matrix.permanent AR := by ring
      _ ≤ Matrix.permanent A * Matrix.permanent BR +
          Matrix.permanent B * Matrix.permanent AR :=
        add_le_add hmulA hmulB
      _ = Matrix.permanent C := by rw [hper]; ring
  exact ⟨hdiag, hwhole, hminor, hpivot, hnrest⟩

end Chollet

#print axioms Chollet.RootStrong.onePointSum
