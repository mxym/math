import PermanentDirectSum
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- All terms in the permanent of an entrywise square are nonnegative. -/
theorem permanent_entrywiseSquare_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    0 ≤ Matrix.permanent (fun i j => A i j * A i j) := by
  classical
  unfold Matrix.permanent
  apply Finset.sum_nonneg
  intro σ _
  apply Finset.prod_nonneg
  intro i _
  simpa [pow_two] using sq_nonneg (A (σ i) i)

/-- Entire strong-Chollet inequality is multiplicative under a direct sum
of arbitrary finite real matrices. No PSD hypothesis or matrix-sign
assumption is required. -/
theorem strongChollet_directSumMatrix
    (A : Matrix α α ℝ) (B : Matrix β β ℝ)
    (hA :
      Matrix.permanent (fun i j => A i j * A i j) ≤
        Matrix.permanent A * (∏ i, A i i))
    (hB :
      Matrix.permanent (fun i j => B i j * B i j) ≤
        Matrix.permanent B * (∏ i, B i i)) :
    Matrix.permanent
        (fun i j => directSumMatrix A B i j * directSumMatrix A B i j)
      ≤ Matrix.permanent (directSumMatrix A B) *
        (∏ i, directSumMatrix A B i i) := by
  classical
  have hsquare :
      (fun i j => directSumMatrix A B i j * directSumMatrix A B i j) =
      directSumMatrix (fun i j => A i j * A i j)
        (fun i j => B i j * B i j) := by
    ext i j
    cases i <;> cases j <;> simp [directSumMatrix]
  have hdiag :
      (∏ i, directSumMatrix A B i i) =
        (∏ i, A i i) * (∏ i, B i i) := by
    rw [Fintype.prod_sum_type]
    rfl
  have hqa := permanent_entrywiseSquare_nonneg A
  have hqb := permanent_entrywiseSquare_nonneg B
  have hqab :
      Matrix.permanent (fun i j => A i j * A i j) *
          Matrix.permanent (fun i j => B i j * B i j) ≤
      (Matrix.permanent A * (∏ i, A i i)) *
          (Matrix.permanent B * (∏ i, B i i)) := by
    exact mul_le_mul hA hB hqb (le_trans hqa hA)
  calc
    Matrix.permanent
        (fun i j => directSumMatrix A B i j * directSumMatrix A B i j)
      = Matrix.permanent (fun i j => A i j * A i j) *
          Matrix.permanent (fun i j => B i j * B i j) := by
            rw [hsquare]
            exact permanent_directSumMatrix
              (fun i j => A i j * A i j)
              (fun i j => B i j * B i j)
    _ ≤ (Matrix.permanent A * (∏ i, A i i)) *
          (Matrix.permanent B * (∏ i, B i i)) := hqab
    _ = Matrix.permanent (directSumMatrix A B) *
        (∏ i, directSumMatrix A B i i) := by
          rw [permanent_directSumMatrix, hdiag]
          ring

end Chollet

#print axioms Chollet.permanent_entrywiseSquare_nonneg
#print axioms Chollet.strongChollet_directSumMatrix
