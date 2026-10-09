import CholletPSDClosures

/-! A nonnegative diagonal extension needs only smaller deleted matrices.
This is the induction interface for arbitrary graph assembly. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
noncomputable section

def MatrixStrong (A : Matrix V V ℝ) : Prop :=
  (squareMatrix A).permanent ≤ A.permanent * ∏ i,A i i

theorem matrixStrong_reindex (A : Matrix V V ℝ) (e : W ≃ V) :
    MatrixStrong (A.submatrix e e) ↔ MatrixStrong A := by
  unfold MatrixStrong
  change (Matrix.permanent (fun i j => squareMatrix A (e i) (e j)) ≤
    Matrix.permanent (fun i j => A (e i) (e j)) * ∏ i,A (e i) (e i)) ↔ _
  rw [permanent_reindex_equiv (squareMatrix A) e,permanent_reindex_equiv A e,
    Equiv.prod_comp e (fun i => A i i)]

theorem matrixStrong_diagonal_extension (A : Matrix V V ℝ) (hA : A.PosSemidef)
    (hwhole : MatrixStrong A)
    (hdeleted : ∀ b : V → ℝ,(∀ i,0 ≤ b i) → ∀ v,
      MatrixStrong (principalExcept (A+Matrix.diagonal b) v))
    (a : V → ℝ) (ha : ∀ i,0 ≤ a i) : MatrixStrong (A+Matrix.diagonal a) := by
  have hS (S : Finset V) : MatrixStrong
      (A+Matrix.diagonal (fun i => if i ∈ S then a i else 0)) := by
    induction S using Finset.induction_on with
    | empty => simpa using hwhole
    | @insert v S hv ih =>
      let b : V → ℝ := fun i => if i ∈ S then a i else 0
      have hb : ∀ i,0 ≤ b i := by intro i; dsimp [b]; split_ifs; exact ha i; rfl
      have hp : (A+Matrix.diagonal b).PosSemidef := hA.add (Matrix.PosSemidef.diagonal hb)
      have he : A+Matrix.diagonal (fun i => if i ∈ insert v S then a i else 0) =
          diagonalBump (A+Matrix.diagonal b) v (a v) := by
        ext i j
        by_cases hiv : i=v
        · subst i
          by_cases hjv : j=v
          · subst j; simp [diagonalBump,b,hv,Matrix.add_apply,Matrix.diagonal_apply]
          · simp [diagonalBump,b,hv,hjv,Matrix.add_apply,Matrix.diagonal_apply,
              Ne.symm hjv]
        · by_cases hij : i=j
          · subst j
            simp [diagonalBump,b,hiv,Matrix.add_apply,Matrix.diagonal_apply]
          · simp [diagonalBump,b,hiv,hij,Matrix.add_apply,Matrix.diagonal_apply]
      rw [he]
      exact strongChollet_diagonalBump_psd _ hp v (a v) (ha v) ih (hdeleted b hb v)
  simpa using hS Finset.univ

end
end Chollet
