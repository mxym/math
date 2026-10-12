import TriangleStieltjes
import DegreePair
import Mathlib.Tactic.FinCases

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem graph_lap_entry (i j : V) :
    (G.lapMatrix ℝ) i j =
      if i = j then (G.degree i : ℝ)
      else if G.Adj i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
  · simp only [SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, if_neg hij]
    by_cases hadj : G.Adj i j <;> simp [hadj]

/-- Ordered principal three-by-three matrix on three distinct ambient
vertices, in the true original graph (degrees not restricted to three). -/
def orderedTripleMatrix (u v w : V) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (G.lapMatrix ℝ) (![u,v,w] i) (![u,v,w] j)


/-- Genuine ambient graph Laplacian, ordered on three distinct vertices:
each offdiagonal magnitude is the 0-1 adjacency indicator, and diagonals
are degrees in the ENTIRE graph. -/
theorem orderedTripleMatrix_eq_stieltjes
    (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    orderedTripleMatrix G u v w =
      stieltjesThree (G.degree u : ℝ) (G.degree v : ℝ) (G.degree w : ℝ)
        (if G.Adj u v then 1 else 0)
        (if G.Adj u w then 1 else 0)
        (if G.Adj v w then 1 else 0) := by
  have hxu : G.Adj v u ↔ G.Adj u v := ⟨(·.symm),(·.symm)⟩
  have hyu : G.Adj w u ↔ G.Adj u w := ⟨(·.symm),(·.symm)⟩
  have hzu : G.Adj w v ↔ G.Adj v w := ⟨(·.symm),(·.symm)⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orderedTripleMatrix, stieltjesThree, graph_lap_entry,
      huv, huw, hvw, huv.symm, huw.symm, hvw.symm,
      hxu, hyu, hzu] <;> split_ifs <;> ring


/-- Every three distinct vertices of ANY finite simple graph satisfy the
strong Chollet inequality on their original-degree principal Laplacian. -/
theorem orderedTripleMatrix_strong (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Matrix.permanent (fun i j =>
        orderedTripleMatrix G u v w i j *
        orderedTripleMatrix G u v w i j) ≤
      Matrix.permanent (orderedTripleMatrix G u v w) *
        ((G.degree u : ℝ)*(G.degree v : ℝ)*(G.degree w : ℝ)) := by
  let x : ℝ := if G.Adj u v then 1 else 0
  let y : ℝ := if G.Adj u w then 1 else 0
  let z : ℝ := if G.Adj v w then 1 else 0
  have hx : 0 ≤ x := by dsimp [x]; split_ifs <;> norm_num
  have hy : 0 ≤ y := by dsimp [y]; split_ifs <;> norm_num
  have hz : 0 ≤ z := by dsimp [z]; split_ifs <;> norm_num
  have haNat := adjacency_pair_le_degree G u v w hvw
  have ha : x+y ≤ (G.degree u : ℝ) := by
    dsimp [x,y]
    exact_mod_cast haNat
  have hvu : G.Adj v u ↔ G.Adj u v := ⟨(·.symm),(·.symm)⟩
  have hbNat : (if G.Adj u v then 1 else 0) +
      (if G.Adj v w then 1 else 0) ≤ G.degree v := by
    simpa only [hvu] using adjacency_pair_le_degree G v u w huw
  have hb : x+z ≤ (G.degree v : ℝ) := by
    dsimp [x,z]
    exact_mod_cast hbNat
  have hwu : G.Adj w u ↔ G.Adj u w := ⟨(·.symm),(·.symm)⟩
  have hwv : G.Adj w v ↔ G.Adj v w := ⟨(·.symm),(·.symm)⟩
  have hcNat : (if G.Adj u w then 1 else 0) +
      (if G.Adj v w then 1 else 0) ≤ G.degree w := by
    simpa only [hwu, hwv] using adjacency_pair_le_degree G w u v huv
  have hc : y+z ≤ (G.degree w : ℝ) := by
    dsimp [y,z]
    exact_mod_cast hcNat
  rw [orderedTripleMatrix_eq_stieltjes G u v w huv huw hvw]
  exact strong_chollet_stieltjes_three
    (G.degree u : ℝ) (G.degree v : ℝ) (G.degree w : ℝ) x y z
    hx hy hz ha hb hc

end Chollet
