import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Chollet

open Matrix

/-- The full weighted three-vertex Laplacian, allowing weights zero. -/
def triangleL (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x+y, -x, -y; -x, x+z, -z; -y, -z, y+z]

private def s01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def s12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
private def s02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

/-- Permanent of any 3x3 real matrix, derived from the genuine
permutation-sum definition (six permutations, no numerical tests). -/
theorem permanent_three_formula (a b c d e f g h i : ℝ) :
  Matrix.permanent !![a,b,c; d,e,f; g,h,i] =
    a*e*i + a*f*h + b*d*i + b*f*g + c*d*h + c*e*g := by
  classical
  unfold Matrix.permanent
  rw [show (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
    {1,s01,s02,s12,s01*s12,s12*s01} by decide]
  simp (config := { decide := true }) [s01, s02, s12,
    Equiv.swap_apply_def, Finset.sum_insert, Fin.prod_univ_succ,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
  ring

/-- Exact strong Chollet slack, valid for arbitrary real edge weights. -/
theorem triangle_laplacian_exact (x y z : ℝ) :
    Matrix.permanent (triangleL x y z) *
        ((x+y)*(x+z)*(y+z)) -
      Matrix.permanent (fun i j =>
        (triangleL x y z) i j * (triangleL x y z) i j) =
      2 * (x*y+x*z+y*z) * (x^2*y^2+x^2*z^2+y^2*z^2) := by
  classical
  have hsquare :
      (fun i j : Fin 3 => (triangleL x y z) i j * (triangleL x y z) i j) =
      !![(x+y)^2, x^2, y^2;
         x^2, (x+z)^2, z^2;
         y^2, z^2, (y+z)^2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triangleL] <;> ring
  rw [hsquare]
  unfold triangleL
  rw [permanent_three_formula, permanent_three_formula]
  ring

/-- Strong Chollet for every nonnegative weighted triangle, with no
strict-positivity assumption on edges and including all sparsifications. -/
theorem triangle_laplacian_strong (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Matrix.permanent (fun i j =>
        (triangleL x y z) i j * (triangleL x y z) i j) ≤
      Matrix.permanent (triangleL x y z) * ((x+y)*(x+z)*(y+z)) := by
  rw [← sub_nonneg]
  rw [triangle_laplacian_exact]
  positivity

end Chollet

#print axioms Chollet.permanent_three_formula
#print axioms Chollet.triangle_laplacian_exact
#print axioms Chollet.triangle_laplacian_strong
