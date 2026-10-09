import CholletGraphSplit

/-! Complete strong Chollet for every finite simple unweighted graph,
including every principal subset with original ambient degrees. -/
set_option autoImplicit false
open scoped BigOperators
universe u
namespace Chollet
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem laplacianDiagonalStrong_all : LaplacianDiagonalStrong G := by
  classical
  have h : ∀ n : ℕ,∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W=n → LaplacianDiagonalStrong H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H _ hsize
      have ih' : SmallerDiagonalStrong.{u} (Fintype.card W) := by
        intro X _ _ K _ hx
        exact ih (Fintype.card X) (by omega) X K rfl
      apply diagonalStrong_of_whole_and_smaller H ih'
      by_cases hsmall : Fintype.card W ≤ 3
      · exact matrixStrong_laplacian_of_strongChollet H (strongChollet_card_le_three H hsmall)
      · by_cases hconn : H.Preconnected
        · by_cases hr : ∀ v : W,(H.induce {w : W | w ≠ v}).Preconnected
          · exact matrixStrong_laplacian_of_strongChollet H
              (strongChollet_vertex_robust H hr (by omega))
          · push_neg at hr
            obtain ⟨v,hv⟩ := hr
            exact matrixStrong_of_vertex_cut H ih' v hv
        · exact matrixStrong_of_disconnected H ih' hconn
  exact h (Fintype.card V) V G rfl

theorem strongChollet_all_graphs : StrongChollet G := by
  intro S
  let e : {v : V // v ∈ S} ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have h := laplacianDiagonalStrong_all (G.comap e) (degreeCorrection G e (fun _ => 0))
    (degreeCorrection_nonneg G e (fun _ => 0) (fun _ => le_rfl))
  rw [← laplacian_diagonal_restriction G e (fun _ => 0)] at h
  simp only [Matrix.diagonal_zero,add_zero] at h
  change MatrixStrong (laplacianPrincipal G S) at h
  have hd (i : {v : V // v ∈ S}) :
      laplacianPrincipal G S i i = (G.degree i.val : ℝ) := by
    simp [laplacianPrincipal,SimpleGraph.lapMatrix,SimpleGraph.degMatrix]
  unfold MatrixStrong at h
  change (squareMatrix (laplacianPrincipal G S)).permanent ≤
    (laplacianPrincipal G S).permanent * ∏ i : {v : V // v ∈ S},(G.degree i.val : ℝ)
  simpa only [hd] using h

end
end Chollet

#print axioms Chollet.laplacianDiagonalStrong_all
#print axioms Chollet.strongChollet_all_graphs
