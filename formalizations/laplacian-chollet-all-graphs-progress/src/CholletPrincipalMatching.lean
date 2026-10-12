import CholletMatchingRestriction
import CholletGraphNormalization

/-! Restriction of the actual ambient-degree fractional matching to every
principal index set, and its normalized permanent lower bound. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet.Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

def principalVertexEmbedding (S : Finset V) : {v : V // v ∈ S} ↪ V :=
  ⟨Subtype.val,Subtype.val_injective⟩

def principalEdgeEmbedding (S : Finset V) : OrientedEdges (G.induce (S : Set V)) ↪
    OrientedEdges G where
  toFun e := ⟨(e.val.1.val,e.val.2.val),e.property⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun e : OrientedEdges G => e.val.1) h
    · apply Subtype.ext
      exact congrArg (fun e : OrientedEdges G => e.val.2) h

theorem fractional_principal_feasible (S : Finset V)
    (hx : OrdinaryFeasible (orientedLoopless G) (fractionalOrientedWeight G)) :
    OrdinaryFeasible (orientedLoopless (G.induce (S : Set V)))
      (fun e => (9 / 10 : ℝ) * degreeKernel G e.val.1.val e.val.2.val) := by
  exact ordinaryFeasible_pullback (orientedLoopless G)
    (orientedLoopless (G.induce (S : Set V)))
    (principalVertexEmbedding S) (principalEdgeEmbedding G S)
    (fun _ => rfl) (fun _ => rfl) (fractionalOrientedWeight G) hx

theorem normalized_principal_log_lower (S : Finset V)
    (hd : ∀ v,2 ≤ G.degree v)
    (hx : OrdinaryFeasible (orientedLoopless G) (fractionalOrientedWeight G)) :
    (4 / 5 : ℝ) * (∑ e : OrientedEdges (G.induce (S : Set V)),
      (degreeKernel G e.val.1.val e.val.2.val)^2) ≤
      Real.log (normalizedLaplacian G S).permanent := by
  have hdpos : ∀ v ∈ S,0 < G.degree v := fun v _ => by have := hd v; omega
  have hs (e : OrientedEdges (G.induce (S : Set V))) :
      ((normalizedLaplacian G S) e.val.1 e.val.2)^2 =
        degreeKernel G e.val.1.val e.val.2.val :=
    normalizedLaplacian_edge_square G S e.val.1 e.val.2 e.property
  have hp := fractional_principal_feasible G S hx
  have hxp : OrdinaryFeasible (orientedLoopless (G.induce (S : Set V)))
      (fun e => (9 / 10 : ℝ) * ((normalizedLaplacian G S) e.val.1 e.val.2)^2) := by
    simpa only [hs] using hp
  have h := oriented_normalized_log_permanent_lower (G.induce (S : Set V))
    (normalizedLaplacian G S) (normalizedLaplacian_psd G S)
    (normalizedLaplacian_diag G S hdpos)
    (fun e => by rw [hs e]; exact degreeKernel_le_quarter G hd _ _) hxp
  simpa only [hs] using h

theorem normalized_principal_log_lower_noncycle (S : Finset V)
    (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Connected)
    (hhigh : ∃ v,3 ≤ G.degree v) :
    (4 / 5 : ℝ) * (∑ e : OrientedEdges (G.induce (S : Set V)),
      (degreeKernel G e.val.1.val e.val.2.val)^2) ≤
      Real.log (normalizedLaplacian G S).permanent :=
  normalized_principal_log_lower G S hd (fractional_ordinary_feasible_noncycle G hd hr hhigh)

end
end Chollet.Matching
