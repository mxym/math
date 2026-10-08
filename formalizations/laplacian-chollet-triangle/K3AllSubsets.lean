import K3
import Reindex
import Induced
import Target
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Chollet

set_option maxHeartbeats 5000000

/-- Every proper vertex subset of any graph on three labeled vertices
has bipartite induced support. -/
theorem proper_induced_bipartite_fin_three
    (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (S : Finset (Fin 3)) (hproper : S ≠ Finset.univ) :
    (G.induce (S : Set (Fin 3))).IsBipartite := by
  classical
  have hssub : S ⊂ (Finset.univ : Finset (Fin 3)) := by
    exact Finset.ssubset_univ_iff.mpr hproper
  have hcard : S.card < 3 := by
    have hh := Finset.card_lt_card hssub
    simpa using hh
  have hsubcard : Fintype.card {v : Fin 3 // v ∈ S} ≤ 2 := by
    simpa using (Nat.le_of_lt_succ hcard)
  exact SimpleGraph.Colorable.mono hsubcard
    ((G.induce (S : Set (Fin 3))).colorable_of_fintype)

/-- The complete three-vertex graph satisfies the full same strong
Chollet target for ALL of its principal submatrices. -/
theorem complete_three_graph_strongChollet :
    StrongChollet (⊤ : SimpleGraph (Fin 3)) := by
  classical
  let G : SimpleGraph (Fin 3) := ⊤
  intro S
  by_cases hfull : S = Finset.univ
  · subst S
    let e : {v : Fin 3 // v ∈ (Finset.univ : Finset (Fin 3))} ≃ Fin 3 :=
      { toFun := Subtype.val
        invFun := fun v => ⟨v, Finset.mem_univ v⟩
        left_inv := by intro v; rfl
        right_inv := by intro v; rfl }
    let L : Matrix (Fin 3) (Fin 3) ℝ := G.lapMatrix ℝ
    have hperm :
        Matrix.permanent
          (fun i j : {v : Fin 3 // v ∈ (Finset.univ : Finset (Fin 3))} =>
             L i.val j.val) = Matrix.permanent L := by
      change Matrix.permanent (fun i j => L (e i) (e j)) = Matrix.permanent L
      exact permanent_reindex_equiv L e
    have hsquare :
        Matrix.permanent
          (fun i j : {v : Fin 3 // v ∈ (Finset.univ : Finset (Fin 3))} =>
             L i.val j.val * L i.val j.val) =
          Matrix.permanent (fun i j : Fin 3 => L i j * L i j) := by
      change Matrix.permanent (fun i j => L (e i) (e j) * L (e i) (e j)) =
        Matrix.permanent (fun i j : Fin 3 => L i j * L i j)
      exact permanent_reindex_equiv (fun i j : Fin 3 => L i j * L i j) e
    have hdegree :
        (∏ i : {v : Fin 3 // v ∈ (Finset.univ : Finset (Fin 3))},
           (G.degree i.val : ℝ)) =
          ∏ i : Fin 3, (G.degree i : ℝ) := by
      change (∏ i : {v : Fin 3 // v ∈ (Finset.univ : Finset (Fin 3))},
          (G.degree (e i) : ℝ)) = ∏ i : Fin 3, (G.degree i : ℝ)
      exact Equiv.prod_comp e (fun i : Fin 3 => (G.degree i : ℝ))
    change Matrix.permanent
        (fun i j : {v : Fin 3 // v ∈ (Finset.univ : Finset (Fin 3))} =>
          L i.val j.val * L i.val j.val) ≤
      Matrix.permanent
        (fun i j : {v : Fin 3 // v ∈ (Finset.univ : Finset (Fin 3))} =>
          L i.val j.val) *
        (∏ i : {v : Fin 3 // v ∈ (Finset.univ : Finset (Fin 3))},
          (G.degree i.val : ℝ))
    rw [hsquare, hperm, hdegree]
    exact complete_three_graph_full_laplacian_strong
  · exact strong_chollet_principal_of_induced_bipartite G S
      (proper_induced_bipartite_fin_three G S hfull)

end Chollet

#print axioms Chollet.proper_induced_bipartite_fin_three
#print axioms Chollet.complete_three_graph_strongChollet
