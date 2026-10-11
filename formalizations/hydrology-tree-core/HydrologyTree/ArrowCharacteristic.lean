import HydrologyTree.ArrowDeterminant

/-! Actual characteristic/cofactor formulas for a root and arbitrary heterogeneous
child blocks. All exceptional spectral points are covered by polynomial identities. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {C : Type*} [Fintype C] [LinearOrder C] {V : C → Type*}
  [∀ c, Fintype (V c)] [∀ c, DecidableEq (V c)]

lemma scalar_sub_arrow (d s : ℝ) (B : ∀ c, Matrix (V c) (V c) ℝ)
    (r : ∀ c, V c) (a f : C → ℝ) :
    Matrix.scalar (Unit ⊕ (Σ c, V c)) s - arrowMatrix d B r a f =
      arrowMatrix (s-d) (fun c => Matrix.scalar (V c) s - B c) r (-a) (-f) := by
  ext i j
  rcases i with i | ⟨c,i⟩ <;> rcases j with j | ⟨e,j⟩
  · cases i; cases j; simp [arrowMatrix, Matrix.scalar_apply]
  · cases i; simp [arrowMatrix, arrowRow, Matrix.scalar_apply, neg_ite]
  · cases j; simp [arrowMatrix, arrowColumn, Matrix.scalar_apply, neg_ite]
  · have h := congrArg (fun M => M ⟨c,i⟩ ⟨e,j⟩) (scalar_sub_dependent_blocks B s)
    simpa only [arrowMatrix, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply, Sum.inr.injEq] using h

/-- Full root characteristic recurrence for an arbitrary finite family, without
nonzero-rate, simple-spectrum, or coprimality assumptions. -/
theorem charpoly_arrowMatrix (d : ℝ) (B : ∀ c, Matrix (V c) (V c) ℝ)
    (r : ∀ c, V c) (a f : C → ℝ) :
    (arrowMatrix d B r a f).charpoly = (X - Polynomial.C d) * (∏ c, (B c).charpoly) -
      ∑ c, Polynomial.C (a c * f c) * diagonalCofactor (B c) (r c) *
        ∏ j ∈ Finset.univ.erase c, (B j).charpoly := by
  have hp : (∏ c, (B c).charpoly).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun c _ => Matrix.charpoly_monic _)
  apply Polynomial.eq_of_infinite_eval_eq
  apply (infinite_nonroots _ hp.ne_zero).mono
  intro s hs
  have hB : ∀ c, (Matrix.scalar (V c) s - B c).det ≠ 0 := by
    intro c
    have hn : (∏ c, ((B c).charpoly).eval s) ≠ 0 := by simpa only [Set.mem_setOf_eq, Polynomial.eval_prod] using hs
    rw [← Matrix.eval_charpoly]
    exact Finset.prod_ne_zero_iff.mp hn c (Finset.mem_univ c)
  have h := det_arrowMatrix_cofactors (s-d)
    (fun c => Matrix.scalar (V c) s - B c) r (-a) (-f) hB
  simpa only [Set.mem_setOf_eq, Matrix.eval_charpoly, scalar_sub_arrow,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_finset_sum, Polynomial.eval_X, Polynomial.eval_C,
    eval_diagonalCofactor, Pi.neg_apply, neg_mul_neg] using h

lemma adjugate_root_block {K W : Type*} [CommRing K] [Fintype W] [DecidableEq W]
    (A : Matrix Unit Unit K) (B : Matrix Unit W K) (C : Matrix W Unit K) (D : Matrix W W K) :
    (Matrix.fromBlocks A B C D).adjugate (.inl ()) (.inl ()) = D.det := by
  rw [Matrix.adjugate_apply]
  have hm : (Matrix.fromBlocks A B C D).updateRow (.inl ()) (Pi.single (.inl ()) 1) =
      Matrix.fromBlocks 1 0 C D := by
    ext i j
    cases i <;> cases j <;> simp [Pi.single_apply, Matrix.one_apply]
  rw [hm, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

/-- The actual root cofactor is the product of the actual child characteristic polynomials. -/
theorem cofactor_arrowMatrix (d : ℝ) (B : ∀ c, Matrix (V c) (V c) ℝ)
    (r : ∀ c, V c) (a f : C → ℝ) :
    diagonalCofactor (arrowMatrix d B r a f) (.inl ()) = ∏ c, (B c).charpoly := by
  rw [diagonalCofactor, arrowMatrix, Matrix.charmatrix_fromBlocks, adjugate_root_block]
  exact charpoly_dependent_blocks B

end HydrologyTree
