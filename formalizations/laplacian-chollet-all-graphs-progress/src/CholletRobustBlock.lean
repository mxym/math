import CholletRegularBlock
import GraphTripleSubset

/-! The terminal branch of vertex-count induction: all deleted graphs
preconnected implies minimum degree two once there are at least four vertices. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem exists_outside_finset (S : Finset V) (hS : S.card < Fintype.card V) :
    ∃ w : V,w ∉ S := by
  by_contra h
  push_neg at h
  have he : S=Finset.univ := by ext v; simp [h v]
  simp [he] at hS

theorem vertex_robust_min_degree_two
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (hn : 4 ≤ Fintype.card V) : ∀ v,2 ≤ G.degree v := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro v
  obtain ⟨w,hw⟩ := exists_ne v
  have hp : ({v,w} : Finset V).card=2 := Finset.card_pair hw.symm
  have hout := exists_outside_finset ({v,w} : Finset V) (by omega)
  obtain ⟨a,ha,haw⟩ := Matching.exists_boundary_ne G hr {v,w} (by omega) hout w (by simp)
  have haS : a=v ∨ a=w := by
    have h := (Finset.mem_filter.mp ha).1
    change a ∈ ({v,w} : Finset V) at h
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  have hav : a=v := haS.resolve_right haw
  subst a
  obtain ⟨u,hu,hvu⟩ := (Finset.mem_filter.mp ha).2
  have huv : u ≠ v := by intro h; subst u; exact hu (by simp)
  have hpu : ({v,u} : Finset V).card=2 := Finset.card_pair huv.symm
  have hout' := exists_outside_finset ({v,u} : Finset V) (by omega)
  obtain ⟨a,ha,hau⟩ := Matching.exists_boundary_ne G hr {v,u} (by omega) hout' u (by simp)
  have haS : a=v ∨ a=u := by
    have h := (Finset.mem_filter.mp ha).1
    change a ∈ ({v,u} : Finset V) at h
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  have hav : a=v := haS.resolve_right hau
  subst a
  obtain ⟨t,ht,hvt⟩ := (Finset.mem_filter.mp ha).2
  have hut : u ≠ t := by intro h; subst t; exact ht (by simp)
  have hsub : ({u,t} : Finset V) ⊆ G.neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hvu
    · exact (G.mem_neighborFinset _ _).mpr hvt
  have h := Finset.card_le_card hsub
  simpa [Finset.card_pair hut] using h

theorem strongChollet_vertex_robust
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (hn : 4 ≤ Fintype.card V) : StrongChollet G := by
  have hd := vertex_robust_min_degree_two G hr hn
  by_cases hh : ∃ v,3 ≤ G.degree v
  · have hc (v : V) : (G.induce {w : V | w ≠ v}).Connected := by
      have hn' : 0 < Fintype.card {w : V // w ≠ v} := by
        rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq]
        omega
      have hn'' : 0 < Fintype.card (↑{w : V | w ≠ v}) := by
        rw [Fintype.card_congr (Equiv.refl _ : (↑{w : V | w ≠ v}) ≃ {w : V // w ≠ v})]
        exact hn'
      haveI : Nonempty (↑{w : V | w ≠ v}) := Fintype.card_pos_iff.mp hn''
      exact ⟨hr v⟩
    exact strongChollet_noncycle_block G hd hc hh
  · have he (v : V) : G.degree v=2 := by
      have hlo := hd v
      have hhi : ¬3 ≤ G.degree v := fun h => hh ⟨v,h⟩
      omega
    exact strongChollet_regular_two_robust G he hr hn

theorem strongChollet_card_le_three (hn : Fintype.card V ≤ 3) : StrongChollet G := by
  intro S
  exact strong_chollet_principal_card_le_three G S
    ((Finset.card_le_card (Finset.subset_univ S)).trans (by simpa using hn))

end
end Chollet
