import CholletMatchingWeights

set_option autoImplicit false
open scoped BigOperators symmDiff
open OAI.MatchingEntropy

namespace Chollet
namespace Matching

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
noncomputable section

def doubled (G : LooplessGraph V E) : LooplessGraph (V × Bool) ((E × Bool) ⊕ V) where
  left := fun e => match e with
    | .inl (e, b) => (G.left e, b)
    | .inr v => (v, false)
  right := fun e => match e with
    | .inl (e, b) => (G.right e, b)
    | .inr v => (v, true)
  loopless := by
    intro e h
    cases e with
    | inl e => exact G.loopless e.1 (congrArg Prod.fst h)
    | inr v => have h' := congrArg Prod.snd h; simp at h'

def doubledWeights (G : LooplessGraph V E) (x : E → ℝ) : (E × Bool) ⊕ V → ℝ
  | .inl (e, _) => x e
  | .inr v => 1 - G.degree x v

def layer (U : Finset (V × Bool)) (b : Bool) : Finset V :=
  Finset.univ.filter fun v => (v, b) ∈ U

@[simp] theorem mem_layer (U : Finset (V × Bool)) (v : V) (b : Bool) :
    v ∈ layer U b ↔ (v, b) ∈ U := by simp [layer]

theorem doubled_degree (G : LooplessGraph V E) (x : E → ℝ) (v : V × Bool) :
    (doubled G).degree (doubledWeights G x) v = 1 := by
  rcases v with ⟨v, b⟩
  unfold LooplessGraph.degree
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  cases b <;>
    simp [doubled, doubledWeights, LooplessGraph.Incident, LooplessGraph.degree]
  all_goals
    change G.degree x v + (1 - G.degree x v) = 1
    ring

theorem doubled_cutMass (G : LooplessGraph V E) (x : E → ℝ)
    (U : Finset (V × Bool)) :
    (doubled G).cutMass (doubledWeights G x) U =
      G.cutMass x (layer U false) + G.cutMass x (layer U true) +
        ∑ v ∈ layer U false ∆ layer U true, (1 - G.degree x v) := by
  have hl (e : E) (b : Bool) :
      (doubled G).Crosses U (.inl (e, b)) ↔ G.Crosses (layer U b) e := by
    simp only [LooplessGraph.Crosses, doubled, mem_layer]
  have hv (v : V) : (doubled G).Crosses U (.inr v) ↔
      v ∈ layer U false ∆ layer U true := by
    simp only [LooplessGraph.Crosses, doubled, Finset.mem_symmDiff, mem_layer]
    tauto
  rw [cutMass_sum, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [hl, hv]
  simp only [Fintype.sum_bool, doubledWeights, Finset.sum_add_distrib]
  have hs : (∑ v : V, if v ∈ layer U false ∆ layer U true then
      1 - G.degree x v else 0) =
      ∑ v ∈ layer U false ∆ layer U true, (1 - G.degree x v) := by
    rw [← Finset.sum_filter]
    simp
  rw [hs, ← cutMass_sum, ← cutMass_sum]
  ring

theorem layer_card_sum (U : Finset (V × Bool)) :
    (layer U false).card + (layer U true).card = U.card := by
  have hu : U.card = ∑ v : V × Bool, if v ∈ U then 1 else 0 := by simp
  rw [hu, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Finset.sum_add_distrib]
  simp [layer, add_comm]

theorem symmDiff_card_identity (A B : Finset V) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have he (v : V) :
      (if v ∈ A ∆ B then 1 else 0) + 2 * (if v ∈ A ∩ B then 1 else 0) =
      (if v ∈ A then 1 else 0) + (if v ∈ B then 1 else 0) := by
    by_cases ha : v ∈ A <;> by_cases hb : v ∈ B <;>
      simp [Finset.mem_symmDiff, ha, hb]
  have h := congrArg (fun f : V → ℕ => ∑ v, f v) (funext he)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simpa only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id] using h

theorem odd_layer_symmDiff (U : Finset (V × Bool)) (hU : Odd U.card) :
    Odd (layer U false ∆ layer U true).card := by
  have h := symmDiff_card_identity (layer U false) (layer U true)
  rw [layer_card_sum] at h
  obtain ⟨k, hk⟩ := hU
  refine ⟨k - (layer U false ∩ layer U true).card, ?_⟩
  omega

/-- Every ordinary feasible vector extends to a perfect-matching feasible
vector on two copies of the graph with vertical slack edges. -/
theorem doubled_feasible (G : LooplessGraph V E) (x : E → ℝ)
    (hx : OrdinaryFeasible G x) :
    doubledWeights G x ∈ (doubled G).constraintPolytope := by
  refine ⟨?_, doubled_degree G x, ?_⟩
  · intro e
    cases e with
    | inl e => exact hx.1 e.1
    | inr v => exact sub_nonneg.mpr (hx.2.1 v)
  · intro U hU
    rw [doubled_cutMass]
    have ho := odd_cut_with_slack G x hx _ (odd_layer_symmDiff U hU)
    have hc := cutMass_symmDiff_le G x hx.1 (layer U false) (layer U true)
    linarith

end
end Matching
end Chollet
