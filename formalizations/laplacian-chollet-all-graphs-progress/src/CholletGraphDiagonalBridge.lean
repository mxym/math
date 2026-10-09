import CholletDiagonalExtension
import CholletGraphNormalization
import CholletMatchingRestriction

/-! Every restriction of a graph Laplacian is the Laplacian of the pulled
back graph plus a nonnegative degree correction. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

def degreeCorrection (e : W ↪ V) (a : V → ℝ) (i : W) : ℝ :=
  (G.degree (e i) : ℝ)-(G.comap e).degree i+a (e i)

theorem degree_comap_le (e : W ↪ V) (i : W) :
    ((G.comap e).degree i : ℝ) ≤ G.degree (e i) := by
  rw [G.degree_eq_sum_if_adj (R := ℝ),(G.comap e).degree_eq_sum_if_adj (R := ℝ)]
  exact Matching.sum_embedding_le e
    (fun j => if G.Adj (e i) j then (1 : ℝ) else 0) (by intro j; split_ifs <;> norm_num)

theorem degreeCorrection_nonneg (e : W ↪ V) (a : V → ℝ) (ha : ∀ i,0 ≤ a i) :
    ∀ i,0 ≤ degreeCorrection G e a i := by
  intro i
  unfold degreeCorrection
  linarith [degree_comap_le G e i,ha (e i)]

theorem laplacian_diagonal_restriction (e : W ↪ V) (a : V → ℝ) :
    (G.lapMatrix ℝ+Matrix.diagonal a).submatrix e e =
      (G.comap e).lapMatrix ℝ+Matrix.diagonal (degreeCorrection G e a) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [SimpleGraph.lapMatrix,SimpleGraph.degMatrix,Matrix.add_apply,
      degreeCorrection]
    ring
  · have hval : e i ≠ e j := fun h => hij (e.injective h)
    simp [SimpleGraph.lapMatrix,SimpleGraph.degMatrix,Matrix.add_apply,
      Matrix.diagonal_apply,hij,hval,SimpleGraph.adjMatrix_apply]

def LaplacianDiagonalStrong : Prop :=
  ∀ a : V → ℝ,(∀ i,0 ≤ a i) → MatrixStrong (G.lapMatrix ℝ+Matrix.diagonal a)

theorem degree_comap_equiv (e : W ≃ V) (i : W) :
    (G.comap e).degree i = G.degree (e i) := by
  let f := SimpleGraph.Embedding.comap e.toEmbedding G
  exact (f.degree_eq_of_neighborSet_subset_range
    (fun w _ => e.surjective w)).symm

theorem laplacian_reindex_equiv (e : W ≃ V) :
    (G.lapMatrix ℝ).submatrix e e = (G.comap e).lapMatrix ℝ := by
  have h := laplacian_diagonal_restriction G e.toEmbedding (fun _ => 0)
  have hz : degreeCorrection G e.toEmbedding (fun _ => 0) = 0 := by
    funext i
    simp [degreeCorrection,degree_comap_equiv G e i]
  rw [hz] at h
  change (G.lapMatrix ℝ+Matrix.diagonal (fun _ => 0)).submatrix e e =
    (G.comap e).lapMatrix ℝ+Matrix.diagonal (fun _ => 0) at h
  simpa only [Matrix.diagonal_zero,add_zero] using h

theorem matrixStrong_laplacian_of_strongChollet (hG : StrongChollet G) :
    MatrixStrong (G.lapMatrix ℝ) := by
  let e : {v : V // v ∈ (Finset.univ : Finset V)} ≃ V :=
    { toFun := Subtype.val
      invFun := fun v => ⟨v,Finset.mem_univ v⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply (matrixStrong_reindex _ e).mp
  have h := hG Finset.univ
  change (squareMatrix (laplacianPrincipal G Finset.univ)).permanent ≤
    (laplacianPrincipal G Finset.univ).permanent *
      ∏ i : {v : V // v ∈ (Finset.univ : Finset V)},(G.degree i.val : ℝ) at h
  change MatrixStrong (laplacianPrincipal G Finset.univ)
  unfold MatrixStrong
  have hd (i : {v : V // v ∈ (Finset.univ : Finset V)}) :
      laplacianPrincipal G Finset.univ i i = (G.degree i.val : ℝ) := by
    simp [laplacianPrincipal,SimpleGraph.lapMatrix,SimpleGraph.degMatrix]
  simpa only [hd] using h

end
end Chollet
