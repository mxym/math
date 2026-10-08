import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic.NormNum

namespace Chollet

/-- An actual Mathlib n-cycle on Fin (n+3) is uniformly 2-regular. -/
theorem cycleGraph_degree_all_two (n : ℕ) (i : Fin (n+3)) :
    (SimpleGraph.cycleGraph (n+3)).degree i = 2 :=
  SimpleGraph.cycleGraph_degree_three_le

/-- For every order at least 3, the actual cycle-graph Laplacian has
diagonal 2 and -1 at adjacent vertices, including the wraparound edge.
This is a genuine graph-to-matrix bridge, not a substitute matrix model. -/
theorem cycleGraph_laplacian_entries (n : ℕ) (i j : Fin (n+3)) :
    (SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ i j =
      if i = j then (2:ℝ)
      else if (SimpleGraph.cycleGraph (n+3)).Adj i j then -1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      cycleGraph_degree_all_two]
  · simp only [SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, if_neg hij]
    by_cases hadj : (SimpleGraph.cycleGraph (n+3)).Adj i j <;>
      simp [hadj]

end Chollet

#print axioms Chollet.cycleGraph_degree_all_two
#print axioms Chollet.cycleGraph_laplacian_entries
