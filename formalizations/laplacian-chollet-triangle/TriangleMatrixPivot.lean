import PermanentTwo
import TrianglePivot
import PermanentDiagonalMinor
import Reindex

namespace Chollet

/-- A canonical equivalence from Fin 2 onto the subtype of Fin 3
obtained by deleting zero, verified by the genuine Fin successor/predecessor. -/
def finTwoExceptZero : Fin 2 ≃ {i : Fin 3 // i ≠ 0} where
  toFun := fun i => ⟨i.succ, Fin.succ_ne_zero i⟩
  invFun := fun i => i.val.pred i.property
  left_inv := by
    intro i
    exact Fin.pred_succ i
  right_inv := by
    intro i
    apply Subtype.ext
    exact Fin.succ_pred i.val i.property

/-- The permanent of the actual principal deletion of the 0th
index of any 3x3 Stieltjes matrix, valid without sign assumptions. -/
theorem permanent_stieltjesThree_exceptZero (a b c x y z : ℝ) :
    Matrix.permanent (principalExcept (stieltjesThree a b c x y z) (0 : Fin 3)) =
      b*c+z^2 := by
  classical
  let M := principalExcept (stieltjesThree a b c x y z) (0 : Fin 3)
  let e := finTwoExceptZero
  have h : (fun i j : Fin 2 => M (e i) (e j)) =
      !![b, -z; -z, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, e, finTwoExceptZero, principalExcept, stieltjesThree]
  have hr := permanent_reindex_equiv M e
  rw [h] at hr
  calc
    Matrix.permanent M = Matrix.permanent !![b,-z;-z,c] := hr.symm
    _ = b*c+z^2 := by
      rw [permanent_two_formula]
      ring

/-- Actual matrix-level singleton permanent pivot (the 0th vertex)
for every 3x3 Stieltjes matrix with the two remaining diagonal
dominance bounds. Unlike the global Lieb theorem this proof is direct. -/
theorem stieltjesThree_zero_pivot (a b c x y z : ℝ)
    (hz : 0 ≤ z) (hb : z ≤ b) (hc : z ≤ c) :
    (stieltjesThree a b c x y z) 0 0 *
      Matrix.permanent (principalExcept
        (stieltjesThree a b c x y z) (0 : Fin 3)) ≤
      Matrix.permanent (stieltjesThree a b c x y z) := by
  have hd : stieltjesThree a b c x y z 0 0 = a := by
    simp [stieltjesThree]
  rw [hd, permanent_stieltjesThree_exceptZero,
    permanent_stieltjesThree]
  exact stieltjes_three_first_pivot a b c x y z hz hb hc

end Chollet

#print axioms Chollet.permanent_stieltjesThree_exceptZero
#print axioms Chollet.stieltjesThree_zero_pivot
