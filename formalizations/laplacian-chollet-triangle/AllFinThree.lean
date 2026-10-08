import GraphMain
import K3AllSubsets
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace Chollet

variable (G : SimpleGraph (Fin 3))

private theorem bipartite_of_missing01 (h01 : ¬ G.Adj 0 1) :
    G.IsBipartite := by
  classical
  have h10 : ¬ G.Adj 1 0 := fun h => h01 h.symm
  let f : Fin 3 → Fin 2 := ![0,0,1]
  refine ⟨f, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [f]

private theorem bipartite_of_missing02 (h02 : ¬ G.Adj 0 2) :
    G.IsBipartite := by
  classical
  have h20 : ¬ G.Adj 2 0 := fun h => h02 h.symm
  let f : Fin 3 → Fin 2 := ![0,1,0]
  refine ⟨f, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [f]

private theorem bipartite_of_missing12 (h12 : ¬ G.Adj 1 2) :
    G.IsBipartite := by
  classical
  have h21 : ¬ G.Adj 2 1 := fun h => h12 h.symm
  let f : Fin 3 → Fin 2 := ![1,0,0]
  refine ⟨f, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [f]

/-- Every graph on three labeled vertices (not only the complete triangle)
satisfies the literal shared strong Chollet target on all principal subsets. -/
theorem strongChollet_fin_three (G : SimpleGraph (Fin 3))
    [DecidableRel G.Adj] : StrongChollet G := by
  classical
  by_cases h01 : G.Adj 0 1
  · by_cases h02 : G.Adj 0 2
    · by_cases h12 : G.Adj 1 2
      · have htop : G = ⊤ := by
          have h10 : G.Adj 1 0 := h01.symm
          have h20 : G.Adj 2 0 := h02.symm
          have h21 : G.Adj 2 1 := h12.symm
          ext i j
          fin_cases i <;> fin_cases j <;> simp_all
        simpa [htop] using complete_three_graph_strongChollet
      · exact strongChollet_of_isBipartite G (bipartite_of_missing12 G h12)
    · exact strongChollet_of_isBipartite G (bipartite_of_missing02 G h02)
  · exact strongChollet_of_isBipartite G (bipartite_of_missing01 G h01)

end Chollet

#print axioms Chollet.strongChollet_fin_three
