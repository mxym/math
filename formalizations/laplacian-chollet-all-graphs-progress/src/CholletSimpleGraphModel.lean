import CholletMatchingPermanent
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! Literal finite simple graphs connected to the proved ordinary matching
library. Both orientations are retained as parallel model edges; weights
are halved accordingly, so no arbitrary edge orientation is required. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet
namespace Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

abbrev OrientedEdges := {p : V×V // G.Adj p.1 p.2}

def orientedLoopless : LooplessGraph V (OrientedEdges G) where
  left e := e.val.1
  right e := e.val.2
  loopless e := e.property.ne

theorem sum_oriented_edges (f : V → V → ℝ) :
    (∑ e : OrientedEdges G,f e.val.1 e.val.2) =
      ∑ u,∑ v,if G.Adj u v then f u v else 0 := by
  classical
  have h := Finset.sum_subtype
    (s := (Finset.univ : Finset (V×V)).filter (fun p => G.Adj p.1 p.2))
    (p := fun p : V×V => G.Adj p.1 p.2)
    (F := inferInstance)
    (fun _ => by simp) (fun p => f p.1 p.2)
  rw [← h,Finset.sum_filter,Fintype.sum_prod_type]

theorem oriented_degree (c : V → V → ℝ) (v : V) :
    (orientedLoopless G).degree (fun e => c e.val.1 e.val.2) v =
      (∑ u,if G.Adj v u then c v u else 0) +
      (∑ u,if G.Adj u v then c u v else 0) := by
  classical
  unfold LooplessGraph.degree
  change (∑ e : OrientedEdges G,
    if e.val.1=v ∨ e.val.2=v then c e.val.1 e.val.2 else 0) = _
  rw [sum_oriented_edges G (fun u w => if u=v ∨ w=v then c u w else 0)]
  have hi (u w : V) :
      (if G.Adj u w then (if u=v ∨ w=v then c u w else 0) else 0) =
      (if u=v then (if G.Adj u w then c u w else 0) else 0) +
      (if w=v then (if G.Adj u w then c u w else 0) else 0) := by
    by_cases hu : u=v <;> by_cases hw : w=v
    · subst u; subst w; simp
    · simp [hu,hw,eq_comm]
    · simp [hu,hw,eq_comm]
    · simp [hu,hw,eq_comm]
  simp_rw [hi,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u w =>
    if u=v then (if G.Adj u w then c u w else 0) else 0)]
  simp

theorem oriented_internal_mass (c : V → V → ℝ) (S : Finset V) :
    internalMass (orientedLoopless G) (fun e => c e.val.1 e.val.2) S =
      ∑ u ∈ S,∑ v ∈ S,if G.Adj u v then c u v else 0 := by
  classical
  unfold internalMass
  change (∑ e : OrientedEdges G,
    if e.val.1∈S ∧ e.val.2∈S then c e.val.1 e.val.2 else 0) = _
  rw [sum_oriented_edges G (fun u v => if u∈S ∧ v∈S then c u v else 0)]
  simp_rw [ite_and]
  have hi (u v : V) :
      (if G.Adj u v then (if u∈S then (if v∈S then c u v else 0) else 0) else 0) =
      (if u∈S then (if v∈S then (if G.Adj u v then c u v else 0) else 0) else 0) := by
    split_ifs <;> rfl
  simp_rw [hi]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  simp_rw [← Finset.sum_filter]
  simp

end
end Matching
end Chollet
