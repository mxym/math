import CofactorOption
import Reindex
import Mathlib.GroupTheory.Perm.Option

namespace Chollet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Delete a single row and the matching column, using the actual
principal-submatrix matrix indexed by a subtype. -/
def principalExcept (A : Matrix n n ℝ) (v : n) :
    Matrix {i : n // i ≠ v} {i : n // i ≠ v} ℝ :=
  fun i j => A i.val j.val

/-- Exact permanent update for ANY finite-index real square matrix:
adding t to the diagonal at v increases the permanent by exactly t times
the permanent of the principal submatrix deleting v. No PSD/nonnegativity
assumptions, no external permanent theorem. -/
theorem permanent_diagonalBump_principal (A : Matrix n n ℝ) (v : n) (t : ℝ) :
    Matrix.permanent (diagonalBump A v t) =
      Matrix.permanent A + t * Matrix.permanent (principalExcept A v) := by
  classical
  let β := {i : n // i ≠ v}
  let f : Option β ≃ n := Equiv.optionSubtypeNe v
  let B : Matrix (Option β) (Option β) ℝ := fun i j => A (f i) (f j)
  have hf : f none = v := Equiv.optionSubtypeNe_none v
  have hiff (i : Option β) : f i = v ↔ i = none := by
    constructor
    · intro h
      apply f.injective
      calc f i = v := h
           _ = f none := hf.symm
    · intro h
      subst i
      exact hf
  have hB : diagonalBump B none t =
      (fun i j : Option β => diagonalBump A v t (f i) (f j)) := by
    ext i j
    change (if i = none ∧ j = none then A (f i) (f j) + t
              else A (f i) (f j)) =
      (if f i = v ∧ f j = v then A (f i) (f j) + t
              else A (f i) (f j))
    have hcond : (i = none ∧ j = none) ↔ (f i = v ∧ f j = v) :=
      and_congr (hiff i).symm (hiff j).symm
    by_cases h : i = none ∧ j = none
    · rcases h with ⟨rfl, rfl⟩
      simp [hf]
    · simp [h, (not_iff_not.mpr hcond).mp h]
  have hperB : Matrix.permanent B = Matrix.permanent A :=
    permanent_reindex_equiv A f
  have hperBump :
      Matrix.permanent (diagonalBump B none t) =
        Matrix.permanent (diagonalBump A v t) := by
    rw [hB]
    exact permanent_reindex_equiv (diagonalBump A v t) f
  have hminor :
      Matrix.permanent (fun i j : β => B (some i) (some j)) =
      Matrix.permanent (principalExcept A v) := by
    rfl
  calc
    Matrix.permanent (diagonalBump A v t)
        = Matrix.permanent (diagonalBump B none t) := hperBump.symm
    _ = Matrix.permanent B + t * fixedDiagonalCoefficient B none :=
      permanent_diagonalBump B none t
    _ = Matrix.permanent A + t * Matrix.permanent (principalExcept A v) := by
      rw [hperB, fixedDiagonalCoefficient_option B, hminor]

end Chollet

#print axioms Chollet.permanent_diagonalBump_principal
