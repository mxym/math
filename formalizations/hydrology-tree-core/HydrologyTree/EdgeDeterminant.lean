import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Exact determinant update and attachment of two matrix blocks by one
bidirected edge. The field lemma only uses invertibility of one block;
polynomial continuation removes this restriction for characteristic matrices. -/
open Matrix
noncomputable section
namespace HydrologyTree

section Ring
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

lemma add_single_eq_updateRow (A : Matrix ι ι R) (i j : ι) (c : R) :
    A + Matrix.single i j c = A.updateRow i (A i + Pi.single j c) := by
  ext k l
  by_cases h : k = i
  · subst k
    simp [Matrix.single_apply, Pi.single_apply, eq_comm]
  · simp [Matrix.single_apply, h, Ne.symm h]

/-- The cofactor determinant identity at every matrix, singular or not. -/
theorem det_add_single (A : Matrix ι ι R) (i j : ι) (c : R) :
    (A + Matrix.single i j c).det = A.det + c * A.adjugate j i := by
  rw [add_single_eq_updateRow, Matrix.det_updateRow_add]
  have hs : (Pi.single j c : ι → R) = c • Pi.single j 1 := by
    funext k
    simp [Pi.single_apply, mul_ite]
  rw [hs, Matrix.det_updateRow_smul, ← Matrix.adjugate_apply]
  simp

theorem det_sub_single (A : Matrix ι ι R) (i j : ι) (c : R) :
    (A - Matrix.single i j c).det = A.det - c * A.adjugate j i := by
  rw [sub_eq_add_neg, Matrix.single_neg, det_add_single]
  ring

end Ring

section Field
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Attach arbitrary blocks through just the specified pair of directed entries.
The diagonals are NOT recomputed; existing exit rates remain in each block. -/
def edgeJoin (A : Matrix ι ι K) (B : Matrix κ κ K) (i : ι) (j : κ) (a f : K) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) K :=
  Matrix.fromBlocks A (Matrix.single i j a) (Matrix.single j i f) B

/-- Exact edge-attachment determinant when one block has nonzero determinant;
no invertibility or nonsingularity of the other block is needed. -/
theorem det_edgeJoin_of_right_ne_zero
    (A : Matrix ι ι K) (B : Matrix κ κ K) (i : ι) (j : κ) (a f : K)
    (hB : B.det ≠ 0) :
    (edgeJoin A B i j a f).det = A.det * B.det - a*f*A.adjugate i i*B.adjugate j j := by
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  rw [edgeJoin, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    Matrix.single_mul_mul_single, det_sub_single]
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  field_simp
  <;> ring

end Field
end HydrologyTree
