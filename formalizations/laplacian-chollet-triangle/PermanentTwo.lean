import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Chollet

/-- Permanent of every 2×2 real matrix, proved from the Mathlib
permutation-sum definition. -/
theorem permanent_two_formula (a b c d : ℝ) :
    Matrix.permanent !![a,b;c,d] = a*d+b*c := by
  classical
  unfold Matrix.permanent
  rw [show (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
    {1, Equiv.swap 0 1} by decide]
  simp (config := {decide := true})
    [Equiv.swap_apply_def, Finset.sum_insert, Fin.prod_univ_succ,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
  ring

end Chollet

#print axioms Chollet.permanent_two_formula
