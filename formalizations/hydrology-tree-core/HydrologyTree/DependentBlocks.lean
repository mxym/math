import HydrologyTree.EdgeCharacteristic
import Mathlib.LinearAlgebra.Matrix.Block

/-! Determinants and inverses of heterogeneous finite diagonal blocks. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {C : Type*} [Fintype C] [LinearOrder C] {V : C → Type*}
  [∀ c, Fintype (V c)] [∀ c, DecidableEq (V c)]

/-- Determinant of a finite family of blocks of arbitrary, possibly different sizes. -/
theorem det_dependent_blocks {R : Type*} [CommRing R]
    (B : (c : C) → Matrix (V c) (V c) R) :
    (Matrix.blockDiagonal' B).det = ∏ c, (B c).det := by
  rw [(Matrix.blockTriangular_blockDiagonal' B).det_fintype]
  apply Finset.prod_congr rfl
  intro c _
  let e : V c ≃ {z : Σ c, V c // z.1 = c} := (Equiv.sigmaSubtype c).symm
  have h := Matrix.det_submatrix_equiv_self e
    ((Matrix.blockDiagonal' B).toSquareBlock Sigma.fst c)
  apply h.symm.trans
  congr 1
  ext i j
  simp [e, Matrix.toSquareBlock_def, Matrix.toSquareBlockProp, Equiv.sigmaSubtype]

lemma scalar_sub_dependent_blocks (B : (c : C) → Matrix (V c) (V c) ℝ) (s : ℝ) :
    Matrix.scalar (Σ c, V c) s - Matrix.blockDiagonal' B =
      Matrix.blockDiagonal' (fun c => Matrix.scalar (V c) s - B c) := by
  change Matrix.scalar (Σ c, V c) s - Matrix.blockDiagonal' B =
    Matrix.blockDiagonal' ((fun c => Matrix.scalar (V c) s) - B)
  rw [Matrix.blockDiagonal'_sub]
  congr 1
  ext ⟨c,i⟩ ⟨d,j⟩
  by_cases h : c = d
  · subst d
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.blockDiagonal'_apply_ne, h]

/-- The characteristic polynomial retains every diagonal block, even at shared roots. -/
theorem charpoly_dependent_blocks (B : (c : C) → Matrix (V c) (V c) ℝ) :
    (Matrix.blockDiagonal' B).charpoly = ∏ c, (B c).charpoly := by
  apply Polynomial.funext
  intro s
  rw [Matrix.eval_charpoly, scalar_sub_dependent_blocks, det_dependent_blocks]
  simp only [Polynomial.eval_prod, Matrix.eval_charpoly]

/-- A proved inverse identity, with nonzero block determinants stated explicitly. -/
theorem inverse_dependent_blocks (B : (c : C) → Matrix (V c) (V c) ℝ)
    (hB : ∀ c, (B c).det ≠ 0) :
    (Matrix.blockDiagonal' B)⁻¹ = Matrix.blockDiagonal' (fun c => (B c)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.blockDiagonal'_mul]
  have he : (fun c => (B c)⁻¹ * B c) = fun c => (1 : Matrix (V c) (V c) ℝ) := by
    funext c
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hB c))
  rw [he]
  exact Matrix.blockDiagonal'_one

end HydrologyTree
