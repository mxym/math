import HydrologyTree.EdgeDeterminant
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots

/-! Characteristic-polynomial attachment by a bidirected edge.
No eigenvalue simplicity, positive rate, or nonzero-rate assumption is needed.
All denominators are removed by a polynomial identity argument. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Actual diagonal cofactor of the characteristic matrix, before cancellation. -/
def diagonalCofactor (A : Matrix ι ι ℝ) (i : ι) : ℝ[X] :=
  (Matrix.charmatrix A).adjugate i i

lemma eval_charmatrix (A : Matrix ι ι ℝ) (s : ℝ) :
    (Polynomial.evalRingHom s).mapMatrix (Matrix.charmatrix A) =
      Matrix.scalar ι s - A := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [RingHom.mapMatrix_apply, Matrix.charmatrix_apply_eq]
  · simp [RingHom.mapMatrix_apply, Matrix.charmatrix_apply_ne, h]

lemma eval_diagonalCofactor (A : Matrix ι ι ℝ) (i : ι) (s : ℝ) :
    (diagonalCofactor A i).eval s = (Matrix.scalar ι s - A).adjugate i i := by
  have h := congrArg (fun M : Matrix ι ι ℝ => M i i)
    ((Polynomial.evalRingHom s).map_adjugate (Matrix.charmatrix A))
  rw [eval_charmatrix] at h
  exact h

lemma scalar_sub_edgeJoin (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (i : ι) (j : κ) (a f s : ℝ) :
    Matrix.scalar (ι ⊕ κ) s - edgeJoin A B i j a f =
      edgeJoin (Matrix.scalar ι s - A) (Matrix.scalar κ s - B) i j (-a) (-f) := by
  ext u v
  cases u <;> cases v <;>
    simp [edgeJoin, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.single_apply, neg_ite]

/-- Every nonzero real polynomial is nonzero at infinitely many points. -/
lemma infinite_nonroots (p : ℝ[X]) (hp : p ≠ 0) :
    Set.Infinite {s : ℝ | p.eval s ≠ 0} := by
  simpa only [Set.compl_setOf, Polynomial.IsRoot] using
    (Polynomial.finite_setOfPred_isRoot hp).infinite_compl

/-- Exact characteristic recurrence for attachment by one bidirected edge.
The original block diagonals, including exit rates, are kept unchanged. -/
theorem charpoly_edgeJoin (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (i : ι) (j : κ) (a f : ℝ) :
    (edgeJoin A B i j a f).charpoly =
      A.charpoly * B.charpoly - C (a*f) * diagonalCofactor A i * diagonalCofactor B j := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (infinite_nonroots B.charpoly (Matrix.charpoly_monic B).ne_zero).mono
  intro s hs
  have hd : (Matrix.scalar κ s - B).det ≠ 0 := by
    rwa [← Matrix.eval_charpoly]
  have h := det_edgeJoin_of_right_ne_zero (Matrix.scalar ι s - A)
    (Matrix.scalar κ s - B) i j (-a) (-f) hd
  simpa only [Set.mem_setOf_eq, Matrix.eval_charpoly, scalar_sub_edgeJoin, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, eval_diagonalCofactor, neg_mul_neg] using h

end HydrologyTree
