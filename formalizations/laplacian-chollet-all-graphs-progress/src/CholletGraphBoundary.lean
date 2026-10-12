import CholletGraphDegreeBounds
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The proper-set part of the two-exception argument, using literal
connectivity after vertex deletion and without graph-theoretic axioms. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet.Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem reachable_closed_predicate {W : Type*} (H : SimpleGraph W) (p : W → Prop)
    (hc : ∀ u v,p u → H.Adj u v → p v) {u v : W}
    (hr : H.Reachable u v) (hu : p u) : p v := by
  obtain ⟨q⟩ := hr
  induction q with
  | nil => exact hu
  | @cons u w v h q ih => exact ih (hc u w hu h)

def boundaryVertices (S : Finset V) : Finset V :=
  S.filter (fun v => ∃ w,w ∉ S ∧ G.Adj v w)

theorem exists_boundary_ne
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (S : Finset V) (hS : 2 ≤ S.card) (hw : ∃ w : V,w ∉ S)
    (v : V) (hv : v ∈ S) : ∃ u ∈ boundaryVertices G S,u ≠ v := by
  obtain ⟨u,hu,huv⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) v
  obtain ⟨w,hw⟩ := hw
  have hwv : w ≠ v := by intro h; subst w; exact hw hv
  by_contra hn
  have hc : ∀ a b : {a : V // a ≠ v},a.val ∈ S →
      (G.induce {w : V | w ≠ v}).Adj a b → b.val ∈ S := by
    intro a b ha hab
    by_contra hb
    apply hn
    exact ⟨a.val,by simp [boundaryVertices,ha,show ∃ t,t ∉ S ∧ G.Adj a.val t from
      ⟨b.val,hb,hab⟩],a.property⟩
  have he := reachable_closed_predicate (G.induce {w : V | w ≠ v})
    (fun a => a.val ∈ S) hc (hr v ⟨u,huv⟩ ⟨w,hwv⟩) hu
  exact hw he

theorem two_le_card_boundaryVertices
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (S : Finset V) (hS : 2 ≤ S.card) (hw : ∃ w : V,w ∉ S) :
    2 ≤ (boundaryVertices G S).card := by
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨u,hu,huv⟩ := exists_boundary_ne G hr S hS hw v hv
  have huS : u ∈ S := (Finset.mem_filter.mp hu).1
  obtain ⟨w,hw',hwu⟩ := exists_boundary_ne G hr S hS hw u huS
  have h := Finset.one_lt_card.mpr ⟨u,hu,w,hw',hwu.symm⟩
  omega

end
end Chollet.Matching
