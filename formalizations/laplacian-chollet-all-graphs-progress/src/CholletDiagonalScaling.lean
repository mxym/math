import CholletPSDClosures

/-! Exact two-sided diagonal scaling for the actual matrix permanent.
The identities also cover empty index types and singular scaling. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

def scaleMatrix (r : V → ℝ) (A : Matrix V V ℝ) : Matrix V V ℝ :=
  fun i j => r i * A i j * r j

theorem permanent_scaleMatrix (r : V → ℝ) (A : Matrix V V ℝ) :
    (scaleMatrix r A).permanent = (∏ i,r i)^2 * A.permanent := by
  unfold Matrix.permanent scaleMatrix
  have ht (σ : Equiv.Perm V) :
      (∏ i,r (σ i) * A (σ i) i * r i) = (∏ i,r i)^2 * (∏ i,A (σ i) i) := by
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Equiv.prod_comp σ r]
    ring
  simp_rw [ht]
  rw [Finset.mul_sum]

theorem diagProduct_scaleMatrix (r : V → ℝ) (A : Matrix V V ℝ) :
    (∏ i,scaleMatrix r A i i) = (∏ i,r i)^2 * (∏ i,A i i) := by
  simp only [scaleMatrix,Finset.prod_mul_distrib]
  ring

theorem squareMatrix_scaleMatrix (r : V → ℝ) (A : Matrix V V ℝ) :
    squareMatrix (scaleMatrix r A) = scaleMatrix (fun i => (r i)^2) (squareMatrix A) := by
  ext i j
  simp only [squareMatrix,scaleMatrix]
  ring

theorem strongChollet_scaleMatrix (r : V → ℝ) (A : Matrix V V ℝ)
    (hA : (squareMatrix A).permanent ≤ A.permanent * ∏ i,A i i) :
    (squareMatrix (scaleMatrix r A)).permanent ≤
      (scaleMatrix r A).permanent * ∏ i,scaleMatrix r A i i := by
  rw [squareMatrix_scaleMatrix,permanent_scaleMatrix,permanent_scaleMatrix,
    diagProduct_scaleMatrix]
  rw [Finset.prod_pow]
  have h := mul_le_mul_of_nonneg_left hA (sq_nonneg ((∏ i,r i)^2))
  convert h using 1 <;> ring

theorem scaleMatrix_posSemidef (r : V → ℝ) (A : Matrix V V ℝ) (hA : A.PosSemidef) :
    (scaleMatrix r A).PosSemidef := by
  have h := hA.mul_mul_conjTranspose_same (Matrix.diagonal r)
  have he : Matrix.diagonal r * A * (Matrix.diagonal r).conjTranspose = scaleMatrix r A := by
    ext i j
    simp [scaleMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rwa [he] at h

end
end Chollet
