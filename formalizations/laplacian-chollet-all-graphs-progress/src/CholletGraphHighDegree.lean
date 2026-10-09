import CholletGraphFeasible
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A connected graph after deletion cannot have a unique vertex of
degree above two. The proof uses the proved handshake and spanning-tree
edge lower bound rather than a path classification. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet.Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem connected_degree_sum_lower {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hH : H.Connected) :
    2 * ((Fintype.card W : ℝ) - 1) ≤ ∑ w,(H.degree w : ℝ) := by
  classical
  have hc := hH.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet] at hc
  have hc' : (Fintype.card W : ℝ) ≤ H.edgeFinset.card + 1 := by exact_mod_cast hc
  have hh := H.sum_degrees_eq_twice_card_edges
  have hh' : (∑ w,(H.degree w : ℝ)) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast hh
  linarith

theorem degree_vertex_deleted (v : V) (u : {u : V // u ≠ v}) :
    ((G.induce {w : V | w ≠ v}).degree u : ℝ) +
      (if G.Adj u.val v then 1 else 0) = (G.degree u.val : ℝ) := by
  classical
  have h := Fintype.sum_eq_add_sum_subtype_ne
    (fun w : V => if G.Adj u.val w then (1 : ℝ) else 0) v
  rw [G.degree_eq_sum_if_adj (R := ℝ) u.val,
    (G.induce {w : V | w ≠ v}).degree_eq_sum_if_adj (R := ℝ) u]
  change (∑ w : {w : V // w ≠ v},if G.Adj u.val w.val then (1 : ℝ) else 0) +
    (if G.Adj u.val v then 1 else 0) = _
  linarith

theorem deleted_neighbor_sum (v : V) :
    (∑ u : {u : V // u ≠ v},if G.Adj u.val v then (1 : ℝ) else 0) =
      (G.degree v : ℝ) := by
  classical
  have h := Fintype.sum_eq_add_sum_subtype_ne
    (fun u : V => if G.Adj v u then (1 : ℝ) else 0) v
  have hi (u : {u : V // u ≠ v}) :
      (if G.Adj u.val v then (1 : ℝ) else 0) =
      (if G.Adj v u.val then 1 else 0) := by
    by_cases ha : G.Adj u.val v
    · simp [ha,ha.symm]
    · have hb : ¬G.Adj v u.val := fun hb => ha hb.symm
      simp [ha,hb]
  simp_rw [hi]
  rw [G.degree_eq_sum_if_adj (R := ℝ) v]
  simpa using h.symm

theorem another_high_degree (v : V) (hv : 3 ≤ G.degree v)
    (hd : ∀ u,2 ≤ G.degree u)
    (hr : (G.induce {w : V | w ≠ v}).Connected) :
    ∃ u : V,u ≠ v ∧ 3 ≤ G.degree u := by
  classical
  by_contra hn
  have he (u : {u : V // u ≠ v}) : G.degree u.val = 2 := by
    have hnot : ¬3 ≤ G.degree u.val := fun h => hn ⟨u.val,u.property,h⟩
    have := hd u.val
    omega
  have hs := connected_degree_sum_lower (G.induce {w : V | w ≠ v}) hr
  have hc : Fintype.card (↑{w : V | w ≠ v}) = Fintype.card {u : V // u ≠ v} :=
    Fintype.card_congr (Equiv.refl _)
  rw [hc] at hs
  have hs' := Finset.sum_congr (s₁ := (Finset.univ : Finset {u : V // u ≠ v})) rfl
    (fun u _ => degree_vertex_deleted G v u)
  simp only [Finset.sum_add_distrib] at hs'
  simp_rw [he] at hs'
  rw [deleted_neighbor_sum] at hs'
  simp only [Nat.cast_ofNat,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs'
  have hsum : (∑ u : {u : V // u ≠ v},((G.induce {w : V | w ≠ v}).degree u : ℝ)) =
      (∑ u : (↑{w : V | w ≠ v}),((G.induce {w : V | w ≠ v}).degree u : ℝ)) := by
    apply Fintype.sum_equiv (Equiv.refl _)
    intro u
    rfl
  rw [hsum] at hs'
  have hv' : (3 : ℝ) ≤ G.degree v := by exact_mod_cast hv
  linarith

end
end Chollet.Matching
