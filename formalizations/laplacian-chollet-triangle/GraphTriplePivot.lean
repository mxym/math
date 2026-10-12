import GraphTriple
import TriangleMatrixPivot

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A three-vertex principal matrix of the Laplacian of ANY finite graph
satisfies the exact singleton permanent-pivot bound at its first index,
even if that triple is a triangle and the entire graph has odd cycles. -/
theorem orderedTripleMatrix_zero_pivot
    (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    orderedTripleMatrix G u v w 0 0 *
      Matrix.permanent (principalExcept (orderedTripleMatrix G u v w)
        (0 : Fin 3)) ≤
      Matrix.permanent (orderedTripleMatrix G u v w) := by
  let z : ℝ := if G.Adj v w then 1 else 0
  have hz : 0 ≤ z := by
    dsimp [z]
    split_ifs <;> norm_num
  have hb : z ≤ (G.degree v : ℝ) := by
    dsimp [z]
    by_cases hadj : G.Adj v w
    · have hdeg : 0 < G.degree v := hadj.degree_pos_left
      have hdegReal : (1:ℝ) ≤ (G.degree v : ℝ) := by
        exact_mod_cast hdeg
      simpa [hadj] using hdegReal
    · simp [hadj]
  have hc : z ≤ (G.degree w : ℝ) := by
    dsimp [z]
    by_cases hadj : G.Adj v w
    · have hdeg : 0 < G.degree w := hadj.symm.degree_pos_left
      have hdegReal : (1:ℝ) ≤ (G.degree w : ℝ) := by
        exact_mod_cast hdeg
      simpa [hadj] using hdegReal
    · simp [hadj]
  rw [orderedTripleMatrix_eq_stieltjes G u v w huv huw hvw]
  exact stieltjesThree_zero_pivot
    (G.degree u : ℝ) (G.degree v : ℝ) (G.degree w : ℝ)
    (if G.Adj u v then 1 else 0)
    (if G.Adj u w then 1 else 0)
    (if G.Adj v w then 1 else 0) hz hb hc

end Chollet

#print axioms Chollet.orderedTripleMatrix_zero_pivot
