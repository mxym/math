import CholletTriangleFreeTrace

/-! A degree-two vertex-robust graph on more than three vertices has no
triangle. This is derived directly from its proper-set boundary theorem. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

def AdjTriangleFree : Prop :=
  ∀ u v w : V,G.Adj u v → G.Adj v w → ¬G.Adj w u

theorem two_neighbors_internal (S : Finset V) (a b c : V)
    (hb : b ∈ S) (hc : c ∈ S) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c) :
    2 ≤ Matching.internalDegree G S a := by
  have hs : ({b,c} : Finset V) ⊆ S.filter (G.Adj a) := by
    intro u hu
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hb,hab⟩
    · exact Finset.mem_filter.mpr ⟨hc,hac⟩
  have h := Finset.card_le_card hs
  simpa [Finset.card_pair hbc,Matching.internalDegree] using h

theorem regular_two_vertex_robust_triangle_free (hd : ∀ v,G.degree v = 2)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (hcard : 4 ≤ Fintype.card V) : AdjTriangleFree G := by
  intro u v w huv hvw hwu
  have huw : u ≠ w := hwu.ne.symm
  have huvne : u ≠ v := huv.ne
  have hvwne : v ≠ w := hvw.ne
  let S : Finset V := {u,v,w}
  have hS : S.card = 3 := by simp [S,huvne,huw,hvwne]
  have hout : ∃ t : V,t ∉ S := by
    by_contra hn
    push_neg at hn
    have he : S = Finset.univ := by ext t; simp [hn t]
    have he' : Fintype.card V = 3 := by simpa [he] using hS
    omega
  have hi (a : V) (ha : a ∈ S) : 2 ≤ Matching.internalDegree G S a := by
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with he | he | he
    · subst a
      exact two_neighbors_internal G S u v w (by simp [S]) (by simp [S]) huv hwu.symm hvwne
    · subst a
      exact two_neighbors_internal G S v u w (by simp [S]) (by simp [S]) huv.symm hvw huw
    · subst a
      exact two_neighbors_internal G S w u v (by simp [S]) (by simp [S]) hwu hvw.symm huvne
  obtain ⟨a,ha,_⟩ := Matching.exists_boundary_ne G hr S (by omega) hout u (by simp [S])
  have hlo := hi a (Finset.mem_filter.mp ha).1
  have hhi := Matching.internalDegree_lt_degree_of_boundary G S a ha
  rw [hd a] at hhi
  omega

theorem normalizedEdgeSquare_trace_three (hG : AdjTriangleFree G) (S : Finset V) :
    ((normalizedEdgeSquare G S)^3).trace = 0 := by
  have hp : (normalizedEdgeSquare G S)^3 =
      normalizedEdgeSquare G S * normalizedEdgeSquare G S * normalizedEdgeSquare G S := by
    rw [show (3 : ℕ) = 2+1 by rfl,pow_succ,pow_two]
  rw [hp]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  by_cases h1 : G.Adj i.val k.val
  · by_cases h2 : G.Adj k.val j.val
    · have h3 : ¬G.Adj j.val i.val := hG i.val k.val j.val h1 h2
      simp [normalizedEdgeSquare,h3]
    · simp [normalizedEdgeSquare,h2]
  · simp [normalizedEdgeSquare,h1]

end
end Chollet
