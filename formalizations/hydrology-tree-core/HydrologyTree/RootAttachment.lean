import HydrologyTree.EdgeCharacteristic
import Mathlib.Tactic.LinearCombination

/-! Characteristic/cofactor recursion at an attachment root. These are identities
of actual matrices and their characteristic adjugates, not recursive stand-ins. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

section Ring
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

lemma adjugate_add_single_self (A : Matrix ι ι R) (i : ι) (c : R) :
    (A + Matrix.single i i c).adjugate i i = A.adjugate i i := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  congr 1
  ext k l
  by_cases h : k = i
  · subst k
    simp
  · simp [Matrix.single_apply, h, Ne.symm h]

lemma adjugate_sub_single_self (A : Matrix ι ι R) (i : ι) (c : R) :
    (A - Matrix.single i i c).adjugate i i = A.adjugate i i := by
  rw [sub_eq_add_neg, Matrix.single_neg, adjugate_add_single_self]

end Ring

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma charmatrix_add_single_self (A : Matrix ι ι ℝ) (i : ι) (c : ℝ) :
    Matrix.charmatrix (A + Matrix.single i i c) =
      Matrix.charmatrix A - Matrix.single i i (C c) := by
  ext k l
  by_cases h : k = l
  · subst l
    by_cases hi : i = k
    · subst i
      simp only [Matrix.charmatrix_apply_eq, Matrix.add_apply,
        Matrix.sub_apply, Matrix.single_apply_same, map_add]
      ring
    · simp [Matrix.charmatrix_apply_eq, Matrix.single_apply, hi]
  · have hz : ¬(i = k ∧ i = l) := by
      rintro ⟨hk,hl⟩
      exact h (hk.symm.trans hl)
    simp [Matrix.charmatrix_apply_ne, h, Matrix.single_apply, hz]

lemma charpoly_add_single_self (A : Matrix ι ι ℝ) (i : ι) (c : ℝ) :
    (A + Matrix.single i i c).charpoly = A.charpoly - C c * diagonalCofactor A i := by
  rw [Matrix.charpoly, charmatrix_add_single_self, det_sub_single]
  rfl

lemma diagonalCofactor_add_single_self (A : Matrix ι ι ℝ) (i : ι) (c : ℝ) :
    diagonalCofactor (A + Matrix.single i i c) i = diagonalCofactor A i := by
  rw [diagonalCofactor, charmatrix_add_single_self, adjugate_sub_single_self]
  rfl

lemma edgeJoin_left_diagonal_add (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (i : ι) (j : κ) (a f c : ℝ) :
    edgeJoin (A + Matrix.single i i c) B i j a f =
      edgeJoin A B i j a f + Matrix.single (Sum.inl i) (Sum.inl i) c := by
  ext k l
  cases k <;> cases l <;> simp [edgeJoin, Matrix.single_apply]

/-- The root cofactor multiplies by the characteristic polynomial of each new
branch. This holds even when branches share roots or the connecting rates vanish. -/
theorem diagonalCofactor_edgeJoin_left (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (i : ι) (j : κ) (a f : ℝ) :
    diagonalCofactor (edgeJoin A B i j a f) (Sum.inl i) =
      diagonalCofactor A i * B.charpoly := by
  have h := charpoly_edgeJoin (A + Matrix.single i i 1) B i j a f
  rw [edgeJoin_left_diagonal_add, charpoly_add_single_self,
    charpoly_add_single_self, diagonalCofactor_add_single_self,
    charpoly_edgeJoin] at h
  norm_num only [map_one, one_mul] at h
  linear_combination -h

/-- Both actual determinant identities required to attach a child at the root. -/
theorem root_attachment_pair (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (i : ι) (j : κ) (a f : ℝ) :
    (edgeJoin A B i j a f).charpoly =
      A.charpoly * B.charpoly - C (a*f) * diagonalCofactor A i * diagonalCofactor B j ∧
    diagonalCofactor (edgeJoin A B i j a f) (Sum.inl i) =
      diagonalCofactor A i * B.charpoly :=
  ⟨charpoly_edgeJoin A B i j a f, diagonalCofactor_edgeJoin_left A B i j a f⟩

end HydrologyTree
