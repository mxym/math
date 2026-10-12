import CholletDiagonalScaling
import CholletGraphDegreeBounds
import Target

/-! Diagonal normalization of the literal principal graph Laplacian.
All degrees are taken in the ambient graph. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

def degreeRoot (S : Finset V) (v : {v : V // v ∈ S}) : ℝ :=
  Real.sqrt (G.degree v.val : ℝ)

def normalizedLaplacian (S : Finset V) :
    Matrix {v : V // v ∈ S} {v : V // v ∈ S} ℝ :=
  scaleMatrix (fun v => (degreeRoot G S v)⁻¹) (laplacianPrincipal G S)

theorem laplacianPrincipal_diag (S : Finset V) (v : {v : V // v ∈ S}) :
    laplacianPrincipal G S v v = (G.degree v.val : ℝ) := by
  simp [laplacianPrincipal,SimpleGraph.lapMatrix,SimpleGraph.degMatrix]

theorem normalizedLaplacian_psd (S : Finset V) : (normalizedLaplacian G S).PosSemidef := by
  apply scaleMatrix_posSemidef
  exact (SimpleGraph.posSemidef_lapMatrix ℝ G).submatrix Subtype.val

theorem degreeRoot_pos (S : Finset V)
    (hd : ∀ v ∈ S,0 < G.degree v) (v : {v : V // v ∈ S}) :
    0 < degreeRoot G S v := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast hd v.val v.property

theorem normalizedLaplacian_diag (S : Finset V)
    (hd : ∀ v ∈ S,0 < G.degree v) (v : {v : V // v ∈ S}) :
    normalizedLaplacian G S v v = 1 := by
  have hr : degreeRoot G S v ≠ 0 := (degreeRoot_pos G S hd v).ne'
  have hrs : (degreeRoot G S v)^2 = (G.degree v.val : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  change (degreeRoot G S v)⁻¹ * laplacianPrincipal G S v v * (degreeRoot G S v)⁻¹ = 1
  rw [laplacianPrincipal_diag,← hrs]
  field_simp

theorem scale_normalizedLaplacian (S : Finset V)
    (hd : ∀ v ∈ S,0 < G.degree v) :
    scaleMatrix (degreeRoot G S) (normalizedLaplacian G S) = laplacianPrincipal G S := by
  ext i j
  have hi : degreeRoot G S i ≠ 0 := (degreeRoot_pos G S hd i).ne'
  have hj : degreeRoot G S j ≠ 0 := (degreeRoot_pos G S hd j).ne'
  simp only [scaleMatrix,normalizedLaplacian]
  field_simp

theorem normalizedLaplacian_edge_square (S : Finset V)
    (i j : {v : V // v ∈ S}) (hij : G.Adj i.val j.val) :
    (normalizedLaplacian G S i j)^2 = Matching.degreeKernel G i.val j.val := by
  have hi : (degreeRoot G S i)^2 = (G.degree i.val : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hj : (degreeRoot G S j)^2 = (G.degree j.val : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hl : laplacianPrincipal G S i j = -1 := by
    simp [laplacianPrincipal,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,
      Matrix.diagonal_apply,SimpleGraph.adjMatrix_apply,hij.ne,hij]
  change ((degreeRoot G S i)⁻¹ * laplacianPrincipal G S i j *
    (degreeRoot G S j)⁻¹)^2 = _
  rw [hl]
  simp only [mul_pow,inv_pow,hi,hj]
  simp [Matching.degreeKernel,mul_inv_rev,mul_comm]

theorem strongChollet_principal_of_normalized (S : Finset V)
    (hd : ∀ v ∈ S,0 < G.degree v)
    (h : (squareMatrix (normalizedLaplacian G S)).permanent ≤
      (normalizedLaplacian G S).permanent) :
    (squareMatrix (laplacianPrincipal G S)).permanent ≤
      (laplacianPrincipal G S).permanent * originalDegreeProduct G S := by
  have hn : (squareMatrix (normalizedLaplacian G S)).permanent ≤
      (normalizedLaplacian G S).permanent * ∏ i,normalizedLaplacian G S i i := by
    simpa [normalizedLaplacian_diag G S hd] using h
  have hs := strongChollet_scaleMatrix (degreeRoot G S) (normalizedLaplacian G S) hn
  rw [scale_normalizedLaplacian G S hd] at hs
  simpa [originalDegreeProduct,laplacianPrincipal_diag] using hs

end
end Chollet
