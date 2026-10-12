import PermanentDiagonalMinor
import BlockClosureAlgebra
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace Chollet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise Hadamard square of a real square matrix. -/
def squareMatrix (A : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => A i j * A i j

theorem squareMatrix_diagonalBump (A : Matrix n n ℝ) (v : n) (t : ℝ) :
    squareMatrix (diagonalBump A v t) =
      diagonalBump (squareMatrix A) v (2*A v v*t+t^2) := by
  ext i j
  by_cases hij : i = v ∧ j = v
  · rcases hij with ⟨rfl,rfl⟩
    simp [squareMatrix, diagonalBump]
    ring
  · simp [squareMatrix, diagonalBump, hij]

private theorem diagProd_diagonalBump (A : Matrix n n ℝ) (v : n) (t : ℝ) :
    (∏ i, diagonalBump A v t i i) =
      (A v v+t) * (∏ i ∈ (Finset.univ : Finset n).erase v, A i i) := by
  classical
  have hfn : (fun i => diagonalBump A v t i i) =
      Function.update (fun i => A i i) v (A v v+t) := by
    funext i
    by_cases hi : i = v
    · subst i
      simp [diagonalBump, Function.update]
    · simp [diagonalBump, Function.update, hi]
  calc
    (∏ i, diagonalBump A v t i i) =
        (∏ i, Function.update (fun i => A i i) v (A v v+t) i) :=
          Finset.prod_congr rfl (fun i _ => congrFun hfn i)
    _ = (A v v+t) *
        (∏ i ∈ (Finset.univ : Finset n).erase v, A i i) := by
          rw [Finset.prod_update_of_mem (Finset.mem_univ v)]
          simp only [Finset.erase_eq]

private theorem diagProd_principalExcept (A : Matrix n n ℝ) (v : n) :
    (∏ i ∈ (Finset.univ : Finset n).erase v, A i i) =
      ∏ i : {i : n // i ≠ v}, principalExcept A v i i := by
  classical
  simpa [principalExcept] using
    (Finset.prod_subtype (s := (Finset.univ : Finset n).erase v)
      (p := fun i : n => i ≠ v)
      (F := Subtype.fintype (fun i : n => i ≠ v))
      (by intro i; simp)
      (fun i => A i i))


/-- The genuine matrix-level diagonal stability theorem. The original
strong inequality, deletion strong inequality and singleton pivot
inequality are explicit hypotheses; none is assumed via a hidden axiom.
Every matrix involved uses the actual Mathlib Matrix.permanent. -/
theorem strongChollet_diagonalBump_of_pivot
    (A : Matrix n n ℝ) (v : n) (t : ℝ)
    (ht : 0 ≤ t)
    (hdiag : ∀ i, 0 ≤ A i i)
    (hstrong :
      Matrix.permanent (squareMatrix A) ≤
        Matrix.permanent A * (∏ i, A i i))
    (hminor :
      Matrix.permanent (squareMatrix (principalExcept A v)) ≤
        Matrix.permanent (principalExcept A v) *
          (∏ i : {i : n // i ≠ v}, principalExcept A v i i))
    (hpivot :
      A v v * Matrix.permanent (principalExcept A v) ≤
        Matrix.permanent A) :
    Matrix.permanent (squareMatrix (diagonalBump A v t)) ≤
      Matrix.permanent (diagonalBump A v t) *
        (∏ i, diagonalBump A v t i i) := by
  classical
  let h : ℝ := ∏ i : {i : n // i ≠ v}, principalExcept A v i i
  have ha : 0 ≤ A v v := hdiag v
  have hh : 0 ≤ h := by
    dsimp [h]
    apply Finset.prod_nonneg
    intro i _
    exact hdiag i.val
  have hprod :
      (∏ i, A i i) = A v v * h := by
    calc
      (∏ i, A i i) =
          A v v * (∏ i ∈ (Finset.univ : Finset n).erase v, A i i) :=
            (Finset.mul_prod_erase (Finset.univ : Finset n)
              (fun i => A i i) (Finset.mem_univ v)).symm
      _ = A v v * h := by rw [diagProd_principalExcept]
  have hprodBump :
      (∏ i, diagonalBump A v t i i) = (A v v + t)*h := by
    rw [diagProd_diagonalBump, diagProd_principalExcept]
  have hperBump :
      Matrix.permanent (diagonalBump A v t) =
        Matrix.permanent A + t * Matrix.permanent (principalExcept A v) :=
    permanent_diagonalBump_principal A v t
  have hperSquareBump :
      Matrix.permanent (squareMatrix (diagonalBump A v t)) =
        Matrix.permanent (squareMatrix A) +
          (2*A v v*t+t^2)*
            Matrix.permanent (squareMatrix (principalExcept A v)) := by
    rw [squareMatrix_diagonalBump, permanent_diagonalBump_principal]
    rfl
  have hs : Matrix.permanent (squareMatrix A) ≤
      (A v v)*h*Matrix.permanent A := by
    calc
      _ ≤ Matrix.permanent A * (∏ i, A i i) := hstrong
      _ = (A v v)*h*Matrix.permanent A := by rw [hprod]; ring
  have hm : Matrix.permanent (squareMatrix (principalExcept A v)) ≤
      h * Matrix.permanent (principalExcept A v) := by
    calc
      _ ≤ Matrix.permanent (principalExcept A v) * h := hminor
      _ = h * Matrix.permanent (principalExcept A v) := mul_comm _ _
  have halg := diagonal_increment_algebra
    (A v v) h
    (Matrix.permanent A)
    (Matrix.permanent (principalExcept A v))
    (Matrix.permanent (squareMatrix A))
    (Matrix.permanent (squareMatrix (principalExcept A v)))
    t ha hh ht hs hm hpivot
  calc
    Matrix.permanent (squareMatrix (diagonalBump A v t)) =
      Matrix.permanent (squareMatrix A) +
        (2*A v v*t+t^2) *
          Matrix.permanent (squareMatrix (principalExcept A v)) :=
      hperSquareBump
    _ ≤ h*(A v v+t)*
        (Matrix.permanent A + t*Matrix.permanent (principalExcept A v)) :=
      halg
    _ = Matrix.permanent (diagonalBump A v t) *
        (∏ i, diagonalBump A v t i i) := by
      rw [hprodBump, hperBump]
      ring

#print axioms Chollet.strongChollet_diagonalBump_of_pivot

end Chollet
