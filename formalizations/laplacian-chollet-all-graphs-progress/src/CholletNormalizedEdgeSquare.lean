import CholletPermanentTraceUpper
import CholletPrincipalMatching

/-! The actual edge-square kernel in every normalized principal Laplacian. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

def normalizedEdgeSquare (S : Finset V) : Matrix {v : V // v ∈ S} {v : V // v ∈ S} ℝ :=
  fun i j => if G.Adj i.val j.val then Matching.degreeKernel G i.val j.val else 0

theorem normalizedEdgeSquare_nonneg (S : Finset V) (i j : {v : V // v ∈ S}) :
    0 ≤ normalizedEdgeSquare G S i j := by
  unfold normalizedEdgeSquare
  split_ifs
  · exact Matching.degreeKernel_nonneg G _ _
  · rfl

theorem normalizedEdgeSquare_symm (S : Finset V) (i j : {v : V // v ∈ S}) :
    normalizedEdgeSquare G S i j = normalizedEdgeSquare G S j i := by
  by_cases ha : G.Adj i.val j.val
  · simp [normalizedEdgeSquare,ha,ha.symm,Matching.degreeKernel_symm G i.val j.val]
  · have hb : ¬G.Adj j.val i.val := fun hb => ha hb.symm
    simp [normalizedEdgeSquare,ha,hb]

theorem normalizedEdgeSquare_diag (S : Finset V) (i : {v : V // v ∈ S}) :
    normalizedEdgeSquare G S i i = 0 := by simp [normalizedEdgeSquare]

theorem normalizedEdgeSquare_row (hd : ∀ v,2 ≤ G.degree v) (S : Finset V)
    (i : {v : V // v ∈ S}) : (∑ j,normalizedEdgeSquare G S i j) ≤ 1 / 2 := by
  have h := Matching.sum_embedding_le (Matching.principalVertexEmbedding S)
    (fun j => if G.Adj i.val j then Matching.degreeKernel G i.val j else 0)
    (fun j => by split_ifs; exact Matching.degreeKernel_nonneg G _ _; rfl)
  exact h.trans (Matching.degreeKernel_row_le_half G hd i.val)

theorem normalizedLaplacian_square (hd : ∀ v,2 ≤ G.degree v) (S : Finset V) :
    squareMatrix (normalizedLaplacian G S) = 1 + normalizedEdgeSquare G S := by
  have hdpos : ∀ v ∈ S,0 < G.degree v := fun v _ => by have := hd v; omega
  ext i j
  by_cases hij : i = j
  · subst j
    simp [squareMatrix,normalizedLaplacian_diag G S hdpos,normalizedEdgeSquare_diag G S,
      Matrix.add_apply]
  · have hijval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    by_cases ha : G.Adj i.val j.val
    · change (normalizedLaplacian G S i j) * (normalizedLaplacian G S i j) = _
      rw [← pow_two,normalizedLaplacian_edge_square G S i j ha]
      simp [Matrix.add_apply,Matrix.one_apply,hij,normalizedEdgeSquare,ha]
    · simp [squareMatrix,normalizedLaplacian,scaleMatrix,laplacianPrincipal,
        SimpleGraph.lapMatrix,SimpleGraph.degMatrix,Matrix.diagonal_apply,
        SimpleGraph.adjMatrix_apply,hijval,ha,normalizedEdgeSquare,Matrix.add_apply,
        Matrix.one_apply,hij]

theorem normalizedEdgeSquare_trace_square (S : Finset V) :
    ((normalizedEdgeSquare G S)^2).trace =
      ∑ e : Matching.OrientedEdges (G.induce (S : Set V)),
        (Matching.degreeKernel G e.val.1.val e.val.2.val)^2 := by
  rw [trace_square_eq_frobeniusSquare _ (normalizedEdgeSquare_symm G S)]
  unfold frobeniusSquare
  have h := Matching.sum_oriented_edges (G.induce (S : Set V))
    (fun i j => (Matching.degreeKernel G i.val j.val)^2)
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases ha : G.Adj i.val j.val <;> simp [normalizedEdgeSquare,SimpleGraph.induce_adj,ha]

theorem normalized_principal_log_upper (hd : ∀ v,2 ≤ G.degree v) (S : Finset V) :
    Real.log (squareMatrix (normalizedLaplacian G S)).permanent ≤
      (19 / 24 : ℝ) * (∑ e : Matching.OrientedEdges (G.induce (S : Set V)),
        (Matching.degreeKernel G e.val.1.val e.val.2.val)^2) := by
  rw [normalizedLaplacian_square G hd S,← normalizedEdgeSquare_trace_square G S]
  exact log_permanent_one_add_upper _ (normalizedEdgeSquare_nonneg G S)
    (normalizedEdgeSquare_symm G S) (normalizedEdgeSquare_diag G S)
    (normalizedEdgeSquare_row G hd S)

end
end Chollet
