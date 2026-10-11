import HydrologyTree.RootAttachment

/-! Exact leaf deletion for the characteristic polynomial of a finite real
matrix. Retained principal diagonals include all original boundary-exit rates. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

abbrev DeletedVertex (l : ι) := {v : ι // v ≠ l}

/-- Explicit reindexing into the retained vertices and the deleted leaf. -/
def deleteVertexEquiv (l : ι) : DeletedVertex l ⊕ Unit ≃ ι where
  toFun := Sum.elim Subtype.val (fun _ => l)
  invFun v := if h : v = l then Sum.inr () else Sum.inl ⟨v,h⟩
  left_inv v := by
    rcases v with v | u
    · simp [Sum.elim, v.property]
    · cases u
      simp [Sum.elim]
  right_inv v := by
    by_cases h : v = l <;> simp [Sum.elim, h]

/-- Literal principal submatrix; its diagonal is not recalculated. -/
def deletedMatrix (A : Matrix ι ι ℝ) (l : ι) :
    Matrix (DeletedVertex l) (DeletedVertex l) ℝ := A.submatrix Subtype.val Subtype.val

def singletonMatrix (d : ℝ) : Matrix Unit Unit ℝ := Matrix.of fun _ _ => d

@[simp] lemma singletonMatrix_charpoly (d : ℝ) :
    (singletonMatrix d).charpoly = X-C d := by
  rw [Matrix.charpoly, Matrix.det_unique]
  simp [singletonMatrix, Matrix.charmatrix_apply_eq]

@[simp] lemma singletonMatrix_cofactor (d : ℝ) :
    diagonalCofactor (singletonMatrix d) () = 1 := by
  rw [diagonalCofactor, Matrix.adjugate_subsingleton]
  rfl

lemma charpoly_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    (A.submatrix e e).charpoly = A.charpoly := by
  exact Matrix.charpoly_reindex e.symm A

/-- A structurally isolated leaf gives the actual edge-join matrix after
reindexing. The premises describe zero entries only, not any determinant formula. -/
theorem leaf_matrix_decomposition (A : Matrix ι ι ℝ) (l p : ι) (hp : p ≠ l)
    (hrow : ∀ v, v ≠ l → A l v = if v = p then A l p else 0)
    (hcol : ∀ v, v ≠ l → A v l = if v = p then A p l else 0) :
    A.submatrix (deleteVertexEquiv l) (deleteVertexEquiv l) =
      edgeJoin (deletedMatrix A l) (singletonMatrix (A l l)) ⟨p,hp⟩ () (A p l) (A l p) := by
  ext u v
  rcases u with u | u <;> rcases v with v | v
  · rfl
  · cases v
    simpa [edgeJoin, deleteVertexEquiv, Sum.elim, Matrix.submatrix_apply, Matrix.single_apply,
      Subtype.ext_iff, eq_comm] using hcol u.val u.property
  · cases u
    simpa [edgeJoin, deleteVertexEquiv, Sum.elim, Matrix.submatrix_apply, Matrix.single_apply,
      Subtype.ext_iff, eq_comm] using hrow v.val v.property
  · cases u
    cases v
    rfl

/-- The exact finite-matrix leaf recurrence, valid at all rates and eigenvalues. -/
theorem charpoly_delete_leaf (A : Matrix ι ι ℝ) (l p : ι) (hp : p ≠ l)
    (hrow : ∀ v, v ≠ l → A l v = if v = p then A l p else 0)
    (hcol : ∀ v, v ≠ l → A v l = if v = p then A p l else 0) :
    A.charpoly = (X-C (A l l)) * (deletedMatrix A l).charpoly -
      C (A p l * A l p) * diagonalCofactor (deletedMatrix A l) ⟨p,hp⟩ := by
  rw [← charpoly_submatrix_equiv A (deleteVertexEquiv l),
    leaf_matrix_decomposition A l p hp hrow hcol, charpoly_edgeJoin,
    singletonMatrix_charpoly, singletonMatrix_cofactor]
  ring

end HydrologyTree
