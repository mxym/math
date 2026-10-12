import PermanentOnePoint
import PermanentDirectSum
import Mathlib.Tactic.Ring

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Exact permanent of the principal deletion of the coalesced root.
This is a true matrix equation, including zero-dimensional cases. -/
theorem onePointSum_rootDeletion_permanent
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ) :
    Matrix.permanent
        (fun i j : α ⊕ β => (onePointSumMatrix A B) (some i) (some j)) =
      Matrix.permanent (fun i j : α => A (some i) (some j)) *
      Matrix.permanent (fun i j : β => B (some i) (some j)) := by
  have h :
      (fun i j : α ⊕ β => (onePointSumMatrix A B) (some i) (some j)) =
      directSumMatrix
        (fun i j : α => A (some i) (some j))
        (fun i j : β => B (some i) (some j)) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [h]
  exact permanent_directSumMatrix _ _

/-- The permanent singleton-pivot lower bound is itself preserved by a
one-point sum, provided the pivot lower bound holds in each block
and both deleted-root permanents are nonnegative.

This is the precise algebraic passage needed to iterate vertex
coalescences: no PSD or matrix permanence theorem is assumed. -/
theorem onePointSum_rootPivot_of_blockPivots
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ)
    (hR1 : 0 ≤ Matrix.permanent (fun i j : α => A (some i) (some j)))
    (hR2 : 0 ≤ Matrix.permanent (fun i j : β => B (some i) (some j)))
    (hpivotA : A none none *
        Matrix.permanent (fun i j : α => A (some i) (some j)) ≤
      Matrix.permanent A)
    (hpivotB : B none none *
        Matrix.permanent (fun i j : β => B (some i) (some j)) ≤
      Matrix.permanent B) :
    (onePointSumMatrix A B) none none *
      Matrix.permanent (fun i j : α ⊕ β =>
        (onePointSumMatrix A B) (some i) (some j)) ≤
        Matrix.permanent (onePointSumMatrix A B) := by
  classical
  let R1 := Matrix.permanent (fun i j : α => A (some i) (some j))
  let R2 := Matrix.permanent (fun i j : β => B (some i) (some j))
  let P1 := Matrix.permanent A
  let P2 := Matrix.permanent B
  have hdiff1 : 0 ≤ P1 - A none none * R1 :=
    sub_nonneg.mpr hpivotA
  have hdiff2 : 0 ≤ P2 - B none none * R2 :=
    sub_nonneg.mpr hpivotB
  have hnonneg :
      0 ≤ (P1 - A none none * R1)*R2 +
        R1*(P2-B none none*R2) :=
    add_nonneg (mul_nonneg hdiff1 hR2) (mul_nonneg hR1 hdiff2)
  have hper : Matrix.permanent (onePointSumMatrix A B) =
      P1 * R2 + R1 * P2 := permanent_onePointSumMatrix A B
  have hminor : Matrix.permanent (fun i j : α ⊕ β =>
        (onePointSumMatrix A B) (some i) (some j)) = R1*R2 :=
    onePointSum_rootDeletion_permanent A B
  rw [hper,hminor]
  change (A none none+B none none)*(R1*R2) ≤ P1*R2+R1*P2
  have hid : P1*R2+R1*P2-(A none none+B none none)*(R1*R2) =
       (P1-A none none*R1)*R2 + R1*(P2-B none none*R2) := by ring
  exact sub_nonneg.mp (hid ▸ hnonneg)

end Chollet

#print axioms Chollet.onePointSum_rootDeletion_permanent
#print axioms Chollet.onePointSum_rootPivot_of_blockPivots
