import MatrixRigidity
open scoped BigOperators ComplexConjugate
namespace FourRowTradeoff
noncomputable section

/-- Necessity at the transition weight, for actual complex matrices. -/
theorem critical_equality_only (A : Mat) (hn : NonzeroRows A)
    (he : ‖A.permanent‖ + (1/2 : ℝ)*‖A.det‖ = (3/2 : ℝ)*rowProduct A) :
    IsFlatRankOne A ∨ IsMonomial A :=
  constant_products_dichotomy A hn (critical_equality_constant_products A hn he)

theorem det_norm_permute_columns (A : Mat) (σ : Equiv.Perm (Fin 4)) :
    ‖(A.submatrix id σ).det‖ = ‖A.det‖ := by
  rw [Matrix.det_permute', norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem rowSq_permute_columns (a : Row) (σ : Equiv.Perm (Fin 4)) :
    rowSq (fun j => a (σ j)) = rowSq a := by
  exact Equiv.sum_comp σ (fun j => Complex.normSq (a j))

theorem rowProduct_permute_columns (A : Mat) (σ : Equiv.Perm (Fin 4)) :
    rowProduct (A.submatrix id σ) = rowProduct A := by
  unfold rowProduct
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg Real.sqrt (rowSq_permute_columns (A i) σ)

theorem rowNorm_diagonal (d : Row) (i : Fin 4) :
    rowNorm (Matrix.diagonal d i) = ‖d i‖ := by
  simp [rowNorm, rowSq, Matrix.diagonal, apply_ite, normSq_as_sq]

theorem rowProduct_diagonal (d : Row) :
    rowProduct (Matrix.diagonal d) = ∏ i, ‖d i‖ := by
  simp only [rowProduct, rowNorm_diagonal]

/-- Every monomial matrix has both normalized coordinates equal to one. -/
theorem monomial_values (A : Mat) (h : IsMonomial A) :
    ‖A.permanent‖ = rowProduct A ∧ ‖A.det‖ = rowProduct A := by
  obtain ⟨σ,hσ⟩ := h
  let d : Row := fun i => A i (σ i)
  have hD : A.submatrix id σ = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [d]
    · have hs : σ j ≠ σ i := fun he => hij (σ.injective he).symm
      simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_apply_ne _ hij]
      exact (hσ i).2 (σ j) hs
  have hp : ‖A.permanent‖ = ∏ i, ‖d i‖ := by
    rw [← Matrix.permanent_permute_rows σ A, hD, Matrix.permanent_diagonal, norm_prod]
  have hd : ‖A.det‖ = ∏ i, ‖d i‖ := by
    rw [← det_norm_permute_columns A σ, hD, Matrix.det_diagonal, norm_prod]
  have hr : rowProduct A = ∏ i, ‖d i‖ := by
    rw [← rowProduct_permute_columns A σ, hD, rowProduct_diagonal]
  exact ⟨hp.trans hr.symm, hd.trans hr.symm⟩

/-- The flat rank-one class attains the other endpoint, without normalization assumptions. -/
theorem flat_values (A : Mat) (h : IsFlatRankOne A) :
    ‖A.permanent‖ = (3/2 : ℝ)*rowProduct A ∧ A.det = 0 := by
  obtain ⟨u,v,hu,hv,hm,hA⟩ := h
  have hper : A.permanent = (24 : ℂ) * (u 0*u 1*u 2*u 3) * (v 0*v 1*v 2*v 3) := by
    rw [permanent_laplace]
    simp [symPair, Fin.sum_univ_succ, Fin.rev, hA]
    ring
  have hdet : A.det = 0 := by
    rw [det_laplace]
    simp [altPair, shuffleSign, Fin.sum_univ_succ, Fin.rev, hA]
    ring
  have hsqr : ∀ i, rowSq (A i) = 4 * Complex.normSq (u i) * Complex.normSq (v 0) := by
    intro i
    simp [rowSq, hA, Complex.normSq_mul, hm]
    ring
  have hn24 : Complex.normSq (24 : ℂ) = 576 := by norm_num [Complex.normSq_apply]
  have hs : Complex.normSq A.permanent = ((3/2 : ℝ)*rowProduct A)^2 := by
    rw [hper, mul_pow, rowProduct_sq]
    simp only [Complex.normSq_mul, hn24, hm, hsqr]
    ring
  rw [normSq_as_sq] at hs
  have hnonneg : 0 ≤ (3/2 : ℝ)*rowProduct A :=
    mul_nonneg (by norm_num) (rowProduct_nonneg A)
  exact ⟨le_antisymm ((sq_le_sq₀ (norm_nonneg _) hnonneg).mp hs.le)
    ((sq_le_sq₀ hnonneg (norm_nonneg _)).mp hs.symm.le), hdet⟩

#print axioms critical_equality_only
#print axioms flat_values
#print axioms monomial_values
end
end FourRowTradeoff
