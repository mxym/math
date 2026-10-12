import CholletNoncycleMatching

/-! Restrict an ordinary fractional matching through injective vertex and
edge embeddings. This will preserve the original ambient-graph degrees. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet.Matching
variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
  [DecidableEq V] [DecidableEq E] [DecidableEq W] [DecidableEq F]
noncomputable section

theorem sum_embedding_le (e : F ↪ E) (g : E → ℝ) (hg : ∀ a,0 ≤ g a) :
    (∑ a,g (e a)) ≤ ∑ a,g a := by
  calc
    _ = ∑ a ∈ Finset.univ.map e,g a := by rw [Finset.sum_map]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => hg a)

theorem ordinaryFeasible_pullback (G : LooplessGraph V E) (H : LooplessGraph W F)
    (v : W ↪ V) (e : F ↪ E)
    (hl : ∀ a,v (H.left a) = G.left (e a))
    (hr : ∀ a,v (H.right a) = G.right (e a)) (x : E → ℝ)
    (hx : OrdinaryFeasible G x) : OrdinaryFeasible H (fun a => x (e a)) := by
  classical
  have hi (a : F) (w : W) : G.Incident (v w) (e a) ↔ H.Incident w a := by
    simp only [LooplessGraph.Incident,← hl a,← hr a,v.injective.eq_iff]
  refine ⟨fun a => hx.1 (e a),?_,?_⟩
  · intro w
    have hs := sum_embedding_le e (fun a => if G.Incident (v w) a then x a else 0)
      (fun a => by split_ifs; exact hx.1 a; rfl)
    simp_rw [hi] at hs
    exact hs.trans (hx.2.1 (v w))
  · intro S hodd
    have hs := sum_embedding_le e
      (fun a => if G.left a ∈ S.map v ∧ G.right a ∈ S.map v then x a else 0)
      (fun a => by split_ifs; exact hx.1 a; rfl)
    simp only [← hl,← hr,Finset.mem_map'] at hs
    have hb := hx.2.2 (S.map v) (by simpa using hodd)
    simp only [Finset.card_map] at hb
    exact hs.trans hb

end
end Chollet.Matching
