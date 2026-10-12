import PermanentOnePoint
import PermanentDirectSum
import PermanentDiagonal
import CofactorOption

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The FULL exact one-point-sum formula for the permanent of the
entrywise-squared coalesced matrix. The cross term 2a1a2 is genuine. -/
theorem permanent_onePointSumMatrix_square
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ) :
    Matrix.permanent (fun i j =>
      onePointSumMatrix A B i j * onePointSumMatrix A B i j) =
      Matrix.permanent (fun i j => A i j * A i j) *
        Matrix.permanent (fun i j : β => B (some i) (some j) * B (some i) (some j)) +
      Matrix.permanent (fun i j : α => A (some i) (some j) * A (some i) (some j)) *
        Matrix.permanent (fun i j => B i j * B i j) +
      2*A none none*B none none*
        (Matrix.permanent (fun i j : α => A (some i) (some j) * A (some i) (some j)) *
         Matrix.permanent (fun i j : β => B (some i) (some j) * B (some i) (some j))) := by
  classical
  let S : Matrix (Option α) (Option α) ℝ :=
    fun i j => A i j * A i j
  let T : Matrix (Option β) (Option β) ℝ :=
    fun i j => B i j * B i j
  let M : Matrix (Option (α ⊕ β)) (Option (α ⊕ β)) ℝ :=
    onePointSumMatrix A B
  let Q : Matrix (Option (α ⊕ β)) (Option (α ⊕ β)) ℝ :=
    onePointSumMatrix S T
  have hsq :
      (fun i j => M i j * M i j) =
        diagonalBump Q none (2*A none none*B none none) := by
    ext i j
    cases i with
    | none =>
      cases j with
      | none => simp [M,Q,S,T,onePointSumMatrix,diagonalBump]; ring
      | some j => cases j <;> simp [M,Q,S,T,onePointSumMatrix,diagonalBump]
    | some i =>
      cases i with
      | inl i =>
        cases j with
        | none => simp [M,Q,S,T,onePointSumMatrix,diagonalBump]
        | some j => cases j <;> simp [M,Q,S,T,onePointSumMatrix,diagonalBump]
      | inr i =>
        cases j with
        | none => simp [M,Q,S,T,onePointSumMatrix,diagonalBump]
        | some j => cases j <;> simp [M,Q,S,T,onePointSumMatrix,diagonalBump]
  have hrest :
      (fun i j : α ⊕ β => Q (some i) (some j)) =
        directSumMatrix
          (fun i j : α => S (some i) (some j))
          (fun i j : β => T (some i) (some j)) := by
    ext i j
    cases i <;> cases j <;> rfl
  have hrestPer :
      Matrix.permanent (fun i j : α ⊕ β => Q (some i) (some j)) =
        Matrix.permanent (fun i j : α => S (some i) (some j)) *
        Matrix.permanent (fun i j : β => T (some i) (some j)) := by
    calc
      _ = Matrix.permanent (directSumMatrix
              (fun i j : α => S (some i) (some j))
              (fun i j : β => T (some i) (some j))) :=
          congrArg Matrix.permanent hrest
      _ = _ := permanent_directSumMatrix _ _
  have hQ :
      Matrix.permanent Q =
        Matrix.permanent S *
          Matrix.permanent (fun i j : β => T (some i) (some j)) +
        Matrix.permanent (fun i j : α => S (some i) (some j)) *
          Matrix.permanent T :=
    permanent_onePointSumMatrix S T
  calc
    Matrix.permanent (fun i j =>
      onePointSumMatrix A B i j * onePointSumMatrix A B i j) =
      Matrix.permanent (diagonalBump Q none (2*A none none*B none none)) :=
        congrArg Matrix.permanent hsq
    _ = Matrix.permanent Q +
        (2*A none none*B none none) *
          Matrix.permanent (fun i j : α ⊕ β => Q (some i) (some j)) := by
            rw [permanent_diagonalBump, fixedDiagonalCoefficient_option]
    _ = _ := by
      rw [hQ, hrestPer]

end Chollet

#print axioms Chollet.permanent_onePointSumMatrix_square
