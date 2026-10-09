import TriangleDiagonal

namespace Chollet

open Matrix

/-- A symmetric real Z-matrix of order three. -/
def stieltjesThree (a b c x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a,-x,-y; -x,b,-z; -y,-z,c]

theorem permanent_stieltjesThree (a b c x y z : ℝ) :
    Matrix.permanent (stieltjesThree a b c x y z) =
      triP a b c x y z := by
  unfold stieltjesThree
  rw [permanent_three_formula]
  unfold triP
  ring

theorem permanent_hadamard_stieltjesThree (a b c x y z : ℝ) :
    Matrix.permanent (fun i j =>
        stieltjesThree a b c x y z i j *
        stieltjesThree a b c x y z i j) =
      triQ a b c x y z := by
  have he :
      (fun i j : Fin 3 =>
          stieltjesThree a b c x y z i j *
          stieltjesThree a b c x y z i j) =
      !![a^2,x^2,y^2; x^2,b^2,z^2; y^2,z^2,c^2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stieltjesThree] <;> ring
  rw [he, permanent_three_formula]
  unfold triQ
  ring

/-- Arbitrary-order-three symmetric diagonally dominant Z-matrices
satisfy strong Chollet, with general nonnegative offdiagonal magnitudes
and arbitrary nonnegative diagonal surpluses. -/
theorem strong_chollet_stieltjes_three (a b c x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : x+y ≤ a) (hb : x+z ≤ b) (hc : y+z ≤ c) :
    Matrix.permanent (fun i j =>
        stieltjesThree a b c x y z i j *
        stieltjesThree a b c x y z i j) ≤
      Matrix.permanent (stieltjesThree a b c x y z) * (a*b*c) := by
  rw [← sub_nonneg]
  rw [permanent_stieltjesThree, permanent_hadamard_stieltjesThree]
  exact three_diagonal_dominant_slack a b c x y z hx hy hz ha hb hc

end Chollet

#print axioms Chollet.strong_chollet_stieltjes_three
