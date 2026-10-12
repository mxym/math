import OnePointRoot
import OnePointRightEquiv
import OnePointLeftEquiv
import PermanentDiagonal

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

attribute [local instance] Classical.propDecidable

/-- A universal, exact one-vertex matrix coalescence formula for the genuine
Mathlib permanent, with no positivity/PSD assumption. -/
theorem permanent_onePointSumMatrix
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ) :
    Matrix.permanent (onePointSumMatrix A B) =
      Matrix.permanent A *
        Matrix.permanent (fun i j : β => B (some i) (some j)) +
      Matrix.permanent (fun i j : α => A (some i) (some j)) *
        Matrix.permanent B := by
  classical
  let R1 := Matrix.permanent (fun i j : α => A (some i) (some j))
  let R2 := Matrix.permanent (fun i j : β => B (some i) (some j))
  have hA : Matrix.permanent (diagonalBump A none (B none none)) =
      Matrix.permanent A + B none none * R1 := by
    rw [permanent_diagonalBump, fixedDiagonalCoefficient_option]
  have hB : Matrix.permanent (diagonalBump B none (A none none)) =
      Matrix.permanent B + A none none * R2 := by
    rw [permanent_diagonalBump, fixedDiagonalCoefficient_option]
  have hleft := onePointSum_preservingLeft_contribution A B
  have hright := onePointSum_preservingRight_contribution A B
  have hoverlap := onePointSum_overlap_contribution A B
  have htotal := onePointSum_permanent_support_decomposition A B
  calc
    Matrix.permanent (onePointSumMatrix A B) =
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        if preservesLeft σ then
          ∏ i, onePointSumMatrix A B (σ i) i else 0) +
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        if preservesRight σ then
          ∏ i, onePointSumMatrix A B (σ i) i else 0) -
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        if preservesLeft σ ∧ preservesRight σ then
          ∏ i, onePointSumMatrix A B (σ i) i else 0) := htotal
    _ = (Matrix.permanent B + A none none * R2) * R1 +
        (Matrix.permanent A + B none none * R1) * R2 -
        (A none none + B none none) * R1 * R2 := by
          rw [hleft, hright, hoverlap, hA, hB]
    _ = Matrix.permanent A * R2 + R1 * Matrix.permanent B := by
      ring
    _ = _ := rfl

end Chollet

#print axioms Chollet.permanent_onePointSumMatrix
