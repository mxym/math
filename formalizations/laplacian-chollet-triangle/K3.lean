import Triangle
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic.FinCases

namespace Chollet

private theorem top3_laplacian_eq :
    ((⊤ : SimpleGraph (Fin 3)).lapMatrix ℝ) = triangleL 1 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleL, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix, SimpleGraph.degree, SimpleGraph.neighborFinset]
  all_goals simp [Finset.card_compl]


/-- Strong Chollet for the actual Mathlib 3-cycle graph Laplacian
(not merely a symbolic surrogate matrix). -/
theorem complete_three_graph_full_laplacian_strong :
    Matrix.permanent (fun i j : Fin 3 =>
        ((⊤ : SimpleGraph (Fin 3)).lapMatrix ℝ) i j *
        ((⊤ : SimpleGraph (Fin 3)).lapMatrix ℝ) i j) ≤
      Matrix.permanent ((⊤ : SimpleGraph (Fin 3)).lapMatrix ℝ) *
        (∏ i : Fin 3, ((⊤ : SimpleGraph (Fin 3)).degree i : ℝ)) := by
  have hprod :
      (∏ i : Fin 3, ((⊤ : SimpleGraph (Fin 3)).degree i : ℝ)) = 8 := by
    norm_num [Fin.prod_univ_succ, SimpleGraph.degree,
      SimpleGraph.neighborFinset, Finset.card_compl]
  rw [top3_laplacian_eq, hprod]
  have h := triangle_laplacian_strong 1 1 1
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms Chollet.complete_three_graph_full_laplacian_strong

end Chollet

#print axioms Chollet.top3_laplacian_eq
