import CholletNormalizedEdgeSquare

/-! Close the genuine all-principal strong Chollet conclusion for the
noncycle-block hypotheses. Arbitrary graph assembly is still separate. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem strongChollet_of_fractional_feasible (hd : ∀ v,2 ≤ G.degree v)
    (hx : Matching.OrdinaryFeasible (Matching.orientedLoopless G)
      (Matching.fractionalOrientedWeight G)) : StrongChollet G := by
  intro S
  change (squareMatrix (laplacianPrincipal G S)).permanent ≤
    (laplacianPrincipal G S).permanent * originalDegreeProduct G S
  have hdpos : ∀ v ∈ S,0 < G.degree v := fun v _ => by have := hd v; omega
  apply strongChollet_principal_of_normalized G S hdpos
  have hu := normalizedLaplacian_diag G S hdpos
  have hlow := Matching.normalized_principal_log_lower G S hd hx
  have hupp := normalized_principal_log_upper G hd S
  have hw : 0 ≤ ∑ e : Matching.OrientedEdges (G.induce (S : Set V)),
      (Matching.degreeKernel G e.val.1.val e.val.2.val)^2 :=
    Finset.sum_nonneg fun e _ => sq_nonneg _
  have hlog : Real.log (squareMatrix (normalizedLaplacian G S)).permanent ≤
      Real.log (normalizedLaplacian G S).permanent := by nlinarith
  have hp := permanent_psd_ge_diag_product _ (normalizedLaplacian_psd G S)
  have hper : 1 ≤ (normalizedLaplacian G S).permanent := by simpa only [hu,Finset.prod_const_one] using hp
  have hsqunit : ∀ i,squareMatrix (normalizedLaplacian G S) i i = 1 := by
    intro i
    simp [squareMatrix,hu]
  have hsqnonneg : ∀ i j,0 ≤ squareMatrix (normalizedLaplacian G S) i j := by
    intro i j
    exact mul_self_nonneg _
  have hsqper := one_le_permanent_unit_diag _ hsqunit hsqnonneg
  exact (Real.log_le_log_iff (lt_of_lt_of_le zero_lt_one hsqper)
    (lt_of_lt_of_le zero_lt_one hper)).mp hlog

theorem strongChollet_noncycle_block (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Connected)
    (hhigh : ∃ v,3 ≤ G.degree v) : StrongChollet G :=
  strongChollet_of_fractional_feasible G hd
    (Matching.fractional_ordinary_feasible_noncycle G hd hr hhigh)

theorem strongChollet_even_vertex_robust (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (heven : Even (Fintype.card V)) : StrongChollet G :=
  strongChollet_of_fractional_feasible G hd
    (Matching.fractional_ordinary_feasible_even G hd hr heven)

theorem strongChollet_large_vertex_robust (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (hlarge : 10 ≤ Fintype.card V) : StrongChollet G :=
  strongChollet_of_fractional_feasible G hd
    (Matching.fractional_ordinary_feasible_large G hd hr hlarge)

end
end Chollet
