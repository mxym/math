import HydrologyTree.PositiveSpectrum

/-! Exact nonpole resolvent expansion of a positive definite real symmetric
matrix, with nonnegative spectral weights summing to one. -/
open Matrix Polynomial Unitary
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma unitary_conjugation_scalar (U : Matrix.unitaryGroup I ℝ) (s : ℝ) :
    conjStarAlgAut ℝ _ U (Matrix.scalar I s) = Matrix.scalar I s := by
  exact (conjStarAlgAut ℝ _ U).toAlgEquiv.commutes s

lemma conjugation_diagonal_entry (U : Matrix.unitaryGroup I ℝ) (d : I → ℝ) (o : I) :
    (conjStarAlgAut ℝ _ U (Matrix.diagonal d)) o o = ∑ i : I, (U o i)^2 * d i := by
  rw [conjStarAlgAut_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_diagonal, Matrix.star_apply, Matrix.conjTranspose_apply, star_trivial]
  ring

/-- The normalization of the observable spectral weights follows from unitarity. -/
lemma unitary_row_squares_sum (U : Matrix.unitaryGroup I ℝ) (o : I) :
    (∑ i : I, (U o i)^2) = 1 := by
  have h := conjugation_diagonal_entry U (fun _ => 1) o
  simpa using h.symm

lemma inverse_diagonal_explicit (d : I → ℝ) (hd : ∀ i, d i ≠ 0) :
    Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) = (1 : Matrix I I ℝ) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [hd]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

/-- True resolvent inverse on the exact nonpole domain. -/
theorem conjugated_diagonal_resolvent (U : Matrix.unitaryGroup I ℝ) (r : I → ℝ)
    (s : ℝ) (hs : ∀ i, s + r i ≠ 0) :
    (Matrix.scalar I s + conjStarAlgAut ℝ _ U (Matrix.diagonal r)) *
      conjStarAlgAut ℝ _ U (Matrix.diagonal (fun i => (s+r i)⁻¹)) = 1 := by
  have he : Matrix.scalar I s + conjStarAlgAut ℝ _ U (Matrix.diagonal r) =
      conjStarAlgAut ℝ _ U (Matrix.diagonal (fun i => s+r i)) := by
    rw [← unitary_conjugation_scalar U s, ← map_add]
    congr 1
    rw [Matrix.scalar_apply, ← Matrix.diagonal_add]
  rw [he, ← map_mul, inverse_diagonal_explicit _ hs, map_one]

/-- Nonnegative unit-mass weights for the actual root inverse of any positive
definite matrix. Coincident eigenvalues and zero observation weights are retained. -/
theorem posDef_resolvent_representation (B : Matrix I I ℝ) (hB : B.PosDef) (o : I) :
    ∃ r w : I → ℝ, (∀ i, 0 < r i) ∧ (∀ i, 0 ≤ w i) ∧
      (∑ i, w i) = 1 ∧
      (-B).charpoly = ∏ i, (X+C (r i)) ∧
      ∀ s : ℝ, (∀ i, s + r i ≠ 0) →
        (Matrix.scalar I s + B)⁻¹ o o = ∑ i, w i / (s+r i) := by
  let U := hB.isHermitian.eigenvectorUnitary
  let r := hB.isHermitian.eigenvalues
  refine ⟨r, fun i => (U o i)^2, hB.eigenvalues_pos, fun i => sq_nonneg _,
    unitary_row_squares_sum U o, charpoly_neg_posDef B hB, ?_⟩
  intro s hs
  have hspec : B = conjStarAlgAut ℝ _ U (Matrix.diagonal r) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hB.isHermitian.spectral_theorem
  have hi := conjugated_diagonal_resolvent U r s hs
  rw [← hspec] at hi
  rw [Matrix.inv_eq_right_inv hi, conjugation_diagonal_entry]
  apply Finset.sum_congr rfl
  intro i _
  exact (div_eq_mul_inv _ _).symm

end HydrologyTree
