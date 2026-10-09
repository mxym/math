import CholletRegularMatching

/-! All principal subsets of a degree-two vertex-robust graph. The small
orders use scaled ordinary matching weights and the vanishing third trace. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem normalized_principal_log_lower_scaled (S : Finset V)
    (hd : ∀ v,2 ≤ G.degree v) (a : ℝ) (ha : 0 ≤ a)
    (hx : Matching.OrdinaryFeasible (Matching.orientedLoopless G)
      (fun e => a*Matching.fractionalOrientedWeight G e)) :
    a*(4/5 : ℝ)*(∑ e : Matching.OrientedEdges (G.induce (S : Set V)),
      (Matching.degreeKernel G e.val.1.val e.val.2.val)^2) ≤
      Real.log (normalizedLaplacian G S).permanent := by
  have hdpos : ∀ v ∈ S,0 < G.degree v := fun v _ => by have := hd v; omega
  have hs (e : Matching.OrientedEdges (G.induce (S : Set V))) :
      ((normalizedLaplacian G S) e.val.1 e.val.2)^2 =
        Matching.degreeKernel G e.val.1.val e.val.2.val :=
    normalizedLaplacian_edge_square G S e.val.1 e.val.2 e.property
  have hp := Matching.ordinaryFeasible_pullback (Matching.orientedLoopless G)
    (Matching.orientedLoopless (G.induce (S : Set V)))
    (Matching.principalVertexEmbedding S) (Matching.principalEdgeEmbedding G S)
    (fun _ => rfl) (fun _ => rfl) (fun e => a*Matching.fractionalOrientedWeight G e) hx
  have hxp : Matching.OrdinaryFeasible (Matching.orientedLoopless (G.induce (S : Set V)))
      (fun e => a*((9/10 : ℝ)*((normalizedLaplacian G S) e.val.1 e.val.2)^2)) := by
    change Matching.OrdinaryFeasible (Matching.orientedLoopless (G.induce (S : Set V)))
      (fun e => a*((9/10 : ℝ)*Matching.degreeKernel G e.val.1.val e.val.2.val)) at hp
    simpa only [hs] using hp
  apply le_trans _ (Matching.log_permanent_ge_fractional
    (Matching.orientedLoopless (G.induce (S : Set V))) _ hxp _
    (normalizedLaplacian_psd G S) (normalizedLaplacian_diag G S hdpos))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have h := mul_le_mul_of_nonneg_left
    (Matching.log_one_add_ge_eight_ninths (sq_nonneg _) (by
      rw [hs e]; exact Matching.degreeKernel_le_quarter G hd _ _))
    (show 0 ≤ a*((9/10 : ℝ)*((normalizedLaplacian G S) e.val.1 e.val.2)^2) by positivity)
  change a*(4/5 : ℝ)*(Matching.degreeKernel G e.val.1.val e.val.2.val)^2 ≤
    a*((9/10 : ℝ)*((normalizedLaplacian G S) e.val.1 e.val.2)^2)*
      Real.log (1+((normalizedLaplacian G S) e.val.1 e.val.2)^2)
  rw [hs e] at h ⊢
  convert h using 1 <;> ring

theorem normalized_principal_log_upper_triangle_free
    (hd : ∀ v,2 ≤ G.degree v) (hG : AdjTriangleFree G) (S : Finset V) :
    Real.log (squareMatrix (normalizedLaplacian G S)).permanent ≤
      (5/8 : ℝ)*(∑ e : Matching.OrientedEdges (G.induce (S : Set V)),
        (Matching.degreeKernel G e.val.1.val e.val.2.val)^2) := by
  rw [normalizedLaplacian_square G hd S,← normalizedEdgeSquare_trace_square G S]
  exact log_permanent_one_add_upper_skip_three _ (normalizedEdgeSquare_nonneg G S)
    (normalizedEdgeSquare_symm G S) (normalizedEdgeSquare_diag G S)
    (normalizedEdgeSquare_row G hd S) (normalizedEdgeSquare_trace_three G hG S)

theorem normalized_square_le_of_log_le (S : Finset V)
    (hdpos : ∀ v ∈ S,0 < G.degree v)
    (hlog : Real.log (squareMatrix (normalizedLaplacian G S)).permanent ≤
      Real.log (normalizedLaplacian G S).permanent) :
    (squareMatrix (normalizedLaplacian G S)).permanent ≤
      (normalizedLaplacian G S).permanent := by
  have hu := normalizedLaplacian_diag G S hdpos
  have hp := permanent_psd_ge_diag_product _ (normalizedLaplacian_psd G S)
  have hper : 1 ≤ (normalizedLaplacian G S).permanent := by
    simpa only [hu,Finset.prod_const_one] using hp
  have hsqunit : ∀ i,squareMatrix (normalizedLaplacian G S) i i = 1 := by
    intro i; simp [squareMatrix,hu]
  have hsqnonneg : ∀ i j,0 ≤ squareMatrix (normalizedLaplacian G S) i j := by
    intro i j; exact mul_self_nonneg _
  have hsqper := one_le_permanent_unit_diag _ hsqunit hsqnonneg
  exact (Real.log_le_log_iff (lt_of_lt_of_le zero_lt_one hsqper)
    (lt_of_lt_of_le zero_lt_one hper)).mp hlog

theorem strongChollet_regular_two_small (hd : ∀ v,G.degree v=2)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (hn : 4 ≤ Fintype.card V) (hn' : Fintype.card V ≤ 10) : StrongChollet G := by
  have hdeg : ∀ v,2 ≤ G.degree v := fun v => by rw [hd v]
  have htri := regular_two_vertex_robust_triangle_free G hd hr hn
  have hx := Matching.fractional_ordinary_feasible_regular_small G hd hr hn hn'
  intro S
  change (squareMatrix (laplacianPrincipal G S)).permanent ≤
    (laplacianPrincipal G S).permanent*originalDegreeProduct G S
  have hdpos : ∀ v ∈ S,0 < G.degree v := fun v _ => by rw [hd v]; omega
  apply strongChollet_principal_of_normalized G S hdpos
  apply normalized_square_le_of_log_le G S hdpos
  have hl := normalized_principal_log_lower_scaled G S hdeg _
    (Matching.regularMatchingScale_nonneg _ hn) hx
  have hu := normalized_principal_log_upper_triangle_free G hdeg htri S
  have hw : 0 ≤ ∑ e : Matching.OrientedEdges (G.induce (S : Set V)),
      (Matching.degreeKernel G e.val.1.val e.val.2.val)^2 :=
    Finset.sum_nonneg fun e _ => sq_nonneg _
  have hc := mul_le_mul_of_nonneg_right
    (Matching.regularMatchingScale_lower_coefficient _ hn) hw
  exact hu.trans (hc.trans hl)

theorem strongChollet_regular_two_robust (hd : ∀ v,G.degree v=2)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (hn : 4 ≤ Fintype.card V) : StrongChollet G := by
  by_cases hl : 10 ≤ Fintype.card V
  · exact strongChollet_large_vertex_robust G (fun v => by rw [hd v]) hr hl
  · exact strongChollet_regular_two_small G hd hr hn (by omega)

end
end Chollet
