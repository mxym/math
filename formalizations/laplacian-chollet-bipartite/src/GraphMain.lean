import Target
import Bipartite

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Literal target statement for every finite bipartite graph, with degrees in
the original graph and arbitrary principal subset, including the empty set. -/
theorem strongChollet_of_isBipartite (hG : G.IsBipartite) :
    StrongChollet G := by
  exact strong_chollet_of_bipartite G hG

end Chollet

#print axioms Chollet.strongChollet_of_isBipartite
#print axioms Chollet.strong_chollet_of_bipartite
