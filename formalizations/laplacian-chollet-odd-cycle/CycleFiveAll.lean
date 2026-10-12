import CycleFiveReal
import Reindex
import Induced
import Target
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace Chollet

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Explicit alternating two-coloring of all vertices other than
one deleted vertex of the five-cycle. -/
def cycleFiveColor (missing w : Fin 5) : Fin 2 :=
  if w = missing then 0
  else if w = missing + 1 then 0
  else if w = missing + 2 then 1
  else if w = missing + 3 then 0
  else 1

/-- For each vertex removed from C5, the remaining induced four-vertex
path is two-colorable. The 5^3 possibilities are checked by Lean's kernel. -/
theorem cycleFiveColor_valid :
    ∀ missing i j : Fin 5,
      i ≠ missing → j ≠ missing →
      (SimpleGraph.cycleGraph 5).Adj i j →
      cycleFiveColor missing i ≠ cycleFiveColor missing j := by
  decide

theorem cycleFive_proper_induced_bipartite (S : Finset (Fin 5))
    (hproper : S ≠ Finset.univ) :
    ((SimpleGraph.cycleGraph 5).induce (S : Set (Fin 5))).IsBipartite := by
  classical
  have hmissing : ∃ v : Fin 5, v ∉ S := by
    by_contra hall
    apply hproper
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact hall ⟨i, hi⟩
  obtain ⟨v, hv⟩ := hmissing
  let coloring : {i : Fin 5 // i ∈ S} → Fin 2 :=
    fun i => cycleFiveColor v i.val
  refine ⟨coloring, ?_⟩
  intro i j hadj
  have hi : i.val ≠ v := fun heq => hv (heq ▸ i.property)
  have hj : j.val ≠ v := fun heq => hv (heq ▸ j.property)
  exact cycleFiveColor_valid v i.val j.val hi hj hadj

/-- The complete original StrongChollet predicate (ALL principal subsets)
for the actual Mathlib five-cycle. This is a nonbipartite graph, not a
bipartite approximation, and it retains degrees of the original graph. -/
theorem cycleFive_all_principal_strongChollet :
    StrongChollet (SimpleGraph.cycleGraph 5) := by
  classical
  let G : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5
  intro S
  by_cases hfull : S = Finset.univ
  · subst S
    let e : {v : Fin 5 // v ∈ (Finset.univ : Finset (Fin 5))} ≃ Fin 5 :=
      { toFun := Subtype.val
        invFun := fun v => ⟨v, Finset.mem_univ v⟩
        left_inv := by intro v; rfl
        right_inv := by intro v; rfl }
    let L : Matrix (Fin 5) (Fin 5) ℝ := G.lapMatrix ℝ
    have hperm :
        Matrix.permanent
          (fun i j : {v : Fin 5 // v ∈ (Finset.univ : Finset (Fin 5))} =>
             L i.val j.val) = Matrix.permanent L := by
      change Matrix.permanent (fun i j => L (e i) (e j)) = Matrix.permanent L
      exact permanent_reindex_equiv L e
    have hsquare :
        Matrix.permanent
          (fun i j : {v : Fin 5 // v ∈ (Finset.univ : Finset (Fin 5))} =>
             L i.val j.val * L i.val j.val) =
          Matrix.permanent (fun i j : Fin 5 => L i j * L i j) := by
      change Matrix.permanent (fun i j => L (e i) (e j) * L (e i) (e j)) =
        Matrix.permanent (fun i j : Fin 5 => L i j * L i j)
      exact permanent_reindex_equiv (fun i j : Fin 5 => L i j * L i j) e
    have hdegree :
        (∏ i : {v : Fin 5 // v ∈ (Finset.univ : Finset (Fin 5))},
           (G.degree i.val : ℝ)) =
          ∏ i : Fin 5, (G.degree i : ℝ) := by
      change (∏ i : {v : Fin 5 // v ∈ (Finset.univ : Finset (Fin 5))},
          (G.degree (e i) : ℝ)) = ∏ i : Fin 5, (G.degree i : ℝ)
      exact Equiv.prod_comp e (fun i : Fin 5 => (G.degree i : ℝ))
    change Matrix.permanent
        (fun i j : {v : Fin 5 // v ∈ (Finset.univ : Finset (Fin 5))} =>
          L i.val j.val * L i.val j.val) ≤
      Matrix.permanent
        (fun i j : {v : Fin 5 // v ∈ (Finset.univ : Finset (Fin 5))} =>
          L i.val j.val) *
        (∏ i : {v : Fin 5 // v ∈ (Finset.univ : Finset (Fin 5))},
          (G.degree i.val : ℝ))
    rw [hsquare, hperm, hdegree]
    exact cycleFive_real_full_chollet
  · exact strong_chollet_principal_of_induced_bipartite G S
      (cycleFive_proper_induced_bipartite S hfull)

end Chollet

#print axioms Chollet.cycleFiveColor_valid
#print axioms Chollet.cycleFive_proper_induced_bipartite
#print axioms Chollet.cycleFive_all_principal_strongChollet
