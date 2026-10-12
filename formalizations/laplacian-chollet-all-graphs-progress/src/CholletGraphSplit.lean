import CholletGraphInductionInterfaces

/-! Split a disconnected graph, or a disconnected vertex deletion, into
literal reachable-component types. No block-tree classification is assumed. -/
set_option autoImplicit false
open scoped BigOperators
universe u
namespace Chollet
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem matrixStrong_of_disconnected
    (ih : SmallerDiagonalStrong.{u} (Fintype.card V))
    (hG : ¬G.Preconnected) : MatrixStrong (G.lapMatrix ℝ) := by
  classical
  have hn : ∃ u v : V,¬G.Reachable u v := by
    simpa only [SimpleGraph.Preconnected,not_forall] using hG
  obtain ⟨u,v,huv⟩ := hn
  let p : V → Prop := fun w => G.Reachable u w
  let e := Equiv.sumCompl p
  have ha : 0 < Fintype.card {w : V // p w} :=
    Fintype.card_pos_iff.mpr ⟨⟨u,SimpleGraph.Reachable.refl u⟩⟩
  have hb : 0 < Fintype.card {w : V // ¬p w} :=
    Fintype.card_pos_iff.mpr ⟨⟨v,huv⟩⟩
  have hc : ∀ a : {w : V // p w},∀ b : {w : V // ¬p w},
      ¬(G.comap e).Adj (.inl a) (.inr b) := by
    intro a b hab
    change G.Adj a.val b.val at hab
    exact b.property (a.property.trans hab.reachable)
  apply (matrixStrong_reindex (G.lapMatrix ℝ) e).mp
  rw [laplacian_reindex_equiv G e]
  exact matrixStrong_directSum_laplacian _ ih (G.comap e)
    (Fintype.card_congr e) ha hb hc

theorem matrixStrong_of_vertex_cut
    (ih : SmallerDiagonalStrong.{u} (Fintype.card V)) (v : V)
    (hG : ¬(G.induce {w : V | w ≠ v}).Preconnected) : MatrixStrong (G.lapMatrix ℝ) := by
  classical
  let W := {w : V // w ≠ v}
  let D := G.comap (Subtype.val : W → V)
  change ¬D.Preconnected at hG
  have hn : ∃ a b : W,¬D.Reachable a b := by
    simpa only [SimpleGraph.Preconnected,not_forall] using hG
  obtain ⟨a,b,hab⟩ := hn
  let p : W → Prop := fun w => D.Reachable a w
  let e : Option ({w : W // p w} ⊕ {w : W // ¬p w}) ≃ V :=
    (Equiv.optionCongr (Equiv.sumCompl p)).trans (Equiv.optionSubtypeNe v)
  have ha : 0 < Fintype.card {w : W // p w} :=
    Fintype.card_pos_iff.mpr ⟨⟨a,SimpleGraph.Reachable.refl a⟩⟩
  have hb : 0 < Fintype.card {w : W // ¬p w} :=
    Fintype.card_pos_iff.mpr ⟨⟨b,hab⟩⟩
  have hc : ∀ l : {w : W // p w},∀ r : {w : W // ¬p w},
      ¬(G.comap e).Adj (some (.inl l)) (some (.inr r)) := by
    intro l r hlr
    change D.Adj l.val r.val at hlr
    exact r.property (l.property.trans hlr.reachable)
  apply (matrixStrong_reindex (G.lapMatrix ℝ) e).mp
  rw [laplacian_reindex_equiv G e]
  exact matrixStrong_onePointSum_laplacian _ ih (G.comap e)
    (Fintype.card_congr e) ha hb hc

end
end Chollet
