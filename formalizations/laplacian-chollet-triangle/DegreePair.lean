import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two distinct candidate neighbors contribute at most their indicators
to the degree in the original ambient graph. -/
theorem adjacency_pair_le_degree (v u w : V) (huw : u ≠ w) :
    (if G.Adj v u then 1 else 0) +
      (if G.Adj v w then 1 else 0) ≤ G.degree v := by
  by_cases hu : G.Adj v u
  · by_cases hw : G.Adj v w
    · have hsub : ({u,w} : Finset V) ⊆ G.neighborFinset v := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with he | he
        · subst t
          exact (G.mem_neighborFinset v u).mpr hu
        · subst t
          exact (G.mem_neighborFinset v w).mpr hw
      have htwo : ({u,w}:Finset V).card = 2 := by
        simp [huw]
      have hle : 2 ≤ G.degree v := by
        calc
          2 = ({u,w}:Finset V).card := htwo.symm
          _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
          _ = G.degree v := rfl
      simpa [hu, hw] using hle
    · have hpos : 0 < G.degree v := hu.degree_pos_left
      simp only [hu, hw, ite_true, ite_false, Nat.add_zero, Nat.zero_add]
      omega
  · by_cases hw : G.Adj v w
    · have hpos : 0 < G.degree v := hw.degree_pos_left
      simp only [hu, hw, ite_true, ite_false, Nat.add_zero, Nat.zero_add]
      omega
    · simp [hu, hw]

end Chollet

#print axioms Chollet.adjacency_pair_le_degree
